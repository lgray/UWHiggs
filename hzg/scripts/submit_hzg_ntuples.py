#!/usr/bin/env python

'''
File: submit_tuplization.py

Author: L. Gray, FNAL

Description: submit UW pattuple jobs via condor.

'''

from RecoLuminosity.LumiDB import argparse
import fnmatch
from UWHiggs.hzg.hzg_pattuples import allTuples
from FinalStateAnalysis.Utilities.version import fsa_version
import os
import sys

parser = argparse.ArgumentParser(description='Build NTuple submission')
parser.add_argument('jobid', help='Job ID identifier')
parser.add_argument('--samples', nargs='+', type=str, required=False,
                    help='Filter samples using list of patterns (shell style)')
parser.add_argument('--subsamples',nargs='+', type=str, required=False,
                    help='Filter subsamples using list of patterns')
parser.add_argument('--diobjects', type=int, default=0,
                    help='run diobjects as well')
args = parser.parse_args()

cfg = '%s/src/FinalStateAnalysis/NtupleTools/test/make_ntuples_cfg.py'\
      %os.environ['CMSSW_BASE']
jobId = args.jobid

def filter_sample(filter,sample):
    if filter:
        passes_wildcard = False
        for pattern in filter:
            if fnmatch.fnmatchcase(sample, pattern):
                passes_wildcard = True
        return passes_wildcard 
    else:
        return True

print " # Job ID: %s Version: %s" % (jobId, fsa_version())
print 'export TERMCAP=screen'
for sample in sorted(allTuples.keys()):
    subsamples = allTuples[sample]

    passes_filter = filter_sample(args.samples,sample)
    
    if not passes_filter:
        continue
    for subsample in subsamples.keys():
        if( subsample != 'tupleName' and
            subsample != 'tupleDate' and
            subsample != 'tupleRoot' ):

            passes_filter = filter_sample(args.subsamples,
                                          subsample)    
            if not passes_filter:
                continue

            for tuple in subsamples[subsample]:
                tupleName = tuple[1:].split('/')[0]
                if 'data' in subsample:
                    tupleName = '.'.join(tuple[1:].split('/')[:2])
                
                submit_dir_base = "/scratch/{logname}/{jobid}"\
                                  "/{sample}.{subsample}.{tupleName}".format(
                    logname = os.environ['LOGNAME'],
                    jobid = jobId,
                    sample = sample,
                    subsample = subsample,
                    tupleName = tupleName
                )            
                
                dag_directory = os.path.join(submit_dir_base, 'dags')
                # Create the dag directory
                print "mkdir -p %s" % dag_directory
                submit_dir = os.path.join(submit_dir_base, 'submit')

                sys.stderr.write('Building sample submit dir %s\n' % (sample))
                if os.path.exists(submit_dir):
                    sys.stderr.write('=> skipping existing submit'\
                                     ' directory for %s\n' % sample)
                    continue            

                final_states = ['eeg','mmg']
                if args.diobjects:
                    final_states.append['ee','mm']
                options = ['channels="%s"'%(','.join(final_states))]
                options.append("eventView=1")
                options.append("reportEvery=1000")
                options.append("maxEvents=-1")
                #so far data is fine, so we don't need to re-run
                #the final state builder
                if 'data' not in subsample:
                    options.append('rerunFSA=1')
                    options.append('rerunMCMatch=1')
                options.append("'inputFiles=$inputFileNames'")
                options.append("'outputFile=$outputFileName'")

                

                farmout_options = []
                farmout_options.append(
                    '--input-dir=root://cmsxrootd.hep.wisc.edu/%s'%(
                    '%s%s/%s-%s'%(subsamples['tupleRoot'],
                                  tuple,
                                  subsamples['tupleDate'],
                                  subsamples['tupleName'])
                    )
                    )

                # Check if we need to use a different DBS
                #if 'dbs' in sample_info:
                #    farmout_options.append(
                #        '--dbs-service-url=http://cmsdbsprod.cern.ch/%s/servlet/DBSServlet'
                #        % sample_info['dbs']
                #    )

                output_dir = '/hdfs/store/user/%s/%s/%s/%s'\
                             %(os.environ['LOGNAME'],
                               jobId,
                               '-'.join([subsample,sample]),
                               '.'.join(tuple[1:].split('/'))
                               )
                
                command = [
                    'farmoutAnalysisJobs',
                    #'--no-shared-fs', # Copy libs to submit dir so we don't kill AFS
                    '--infer-cmssw-path',
                    '--vsize-limit=30000',
                    '--express-queue',
                    '--input-files-per-job=1',
                    '"--output-dir=srm://cmssrm.hep.wisc.edu:8443/srm/v2/server?SFN=%s"' % output_dir,
                    '--submit-dir=%s' % submit_dir,
                    '--output-dag-file=%s/dag.dag' % dag_directory,
                    ]
                
                command.extend(farmout_options)
                
                command.append('-'.join([jobId, tupleName]))
                command.append(cfg)
                command.extend(options)
                print ' '.join(command)
