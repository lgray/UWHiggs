#!/usr/bin/env python

#ROOT and low level analysis objects


#from rootpy.utils import asrootpy
#from rootpy.tree import tree
#from rootpy.io import open as ropen
from UWHiggs.hzg.MOOSEY.trees import tree_manager
from UWHiggs.hzg.MOOSEY.cuts import CompositeCutflow

import ROOT
from ROOT import TTree, TFile, TLorentzVector, TVector3, \
     TRandom3, TH1I, TList

#general cutsets
from UWHiggs.hzg.hzg_cuts import muon_triggers_data,muon_triggers_mc, \
     electron_triggers_data, electron_triggers_mc, \
     e_cuts_data_2012,e_cuts_mc_2012, \
     mu_cuts_data,mu_cuts_mc,e_cuts_data,e_cuts_mc, photon_cuts_data, \
     photon_cuts_noifsr, mumu_cuts,ee_cuts,ell_gamma_dr, event_has_ifsr, \
     photon_cuts_mc,photon_cuts_plj,mu_cuts_data_2012,mu_cuts_mc_2012

#correction layer
from UWHiggs.hzg.corrections import setup_corrections

#categorization
from UWHiggs.hzg.categories import hzg_4cat_r9based, hzg_4cat_r9based_mod

#pileup reweighting
from UWHiggs.hzg.pu_reweighting import pu_S10_CD_reweight, puhistos

#luminosity
from UWHiggs.hzg.hzg_intlumis import hzg_lumi, hzg_run_indices, hzg_run_probs

#python standard things
from UWHiggs.hzg.argparse import ArgumentParser
from math import fabs, ceil
import os,sys
import numpy as np

#definitions of various tree types
import UWHiggs.hzg.result_trees as outTrees

#processes one input file
#plans are to have concatenation
#options are:
# --runType={data,A,B,AB}
# --leptonType={muon,electron}
#special modes
# --calcCS, implies two more options, --dataInput --signalMC

muonBranches = ['nMu','muPt','muEta','muPhi','muType',
                'muNumberOfValidMuonHits',
                'muNumberOfValidTrkHits','muNumberOfValidPixelHits',
                'muStations','muChi2NDF','muPVD0','muPVDz',
                'muIsoTrk','muIsoEcal','muIsoHcal',
                'nZmumu','ZmumuLeg1Index','ZmumuLeg2Index','ZmumuMass']

electronBranches = ['nEle','elePt','eleEta','elePhi',
                    'eleE3x3','eleSCEta','eleSCEn','eleSCRawEn',
                    'eleConvMissinghit','eleConvDist','eleConvDcot',
                    'eleSigmaIEtaIEta','eledPhiAtVtx','eledEtaAtVtx','elePVD0',
                    'elePVDz','eleIsoTrkDR03','eleIsoEcalDR03',
                    'eleIsoHcalSolidDR03','eleGenIndex','eleGenGMomPID',
                    'nZee','ZeeLeg1Index','ZeeLeg2Index','ZeeMass']

commonBranches = ['run','lumis','event',
                  'HLT','HLTIndex','HLTprescale','nGoodVtx','IsTracksGood',
                  'rho','nPU',
                  'mcIndex','mcPt','mcEta','mcPhi','mcMass',
                  'nMC','mcPID','mcGMomPID',
                  'nPho','phoEt','phoEta','phoPhi','phoSCEta',
                  'phoHoverE','phohasPixelSeed','phoTrkIsoHollowDR04',
                  'phoEcalIsoDR04','phoHcalIsoDR04',
                  'phoSigmaIEtaIEta','phoSigmaIPhiIPhi','phoR9',
                  'phoGenIndex','phoGenGMomPID','phoGenMomPID',
                  'eleTrg','muTrg']

z_infos = {'electron':{'nZ':'nZee',
                       'ell1':'ZeeLeg1Index',
                       'ell2':'ZeeLeg2Index',
                       'mass':'ZeeMass'},
           'muon':{'nZ':'nZmumu',
                   'ell1':'ZmumuLeg1Index',
                   'ell2':'ZmumuLeg2Index',
                   'mass':'ZmumuMass'}}

lepton_masses = {'electron':5.11e-4,'muon':1.06e-1} # in GeV
lepton_infos = {'electron':{'nEll':'nEle',
                            'pt':'elePt',
                            'corpt':'eleCorPt',
                            'eta':'eleEta',
                            'phi':'elePhi'},
                'muon':{'nEll':'nMu',
                        'pt':'muPt',
                        'corpt':'muPt',
                        'eta':'muEta',
                        'phi':'muPhi'}}

run_lumi = hzg_lumi

rng = TRandom3(0)
             
Z_POLE = 91.188
ell1,ell2,pho = TLorentzVector(),TLorentzVector(),TLorentzVector()
thez, thezg = TLorentzVector(),TLorentzVector()
def run_analysis(options,args):    
    tm = tree_manager()
    pu_weight_sum = 0.0
    selected_events = []
    metaInfoTrees = []
    nEvents_total = int(0)
    pwd = ROOT.gDirectory.GetPath()
    for kFile,input_file in enumerate(args):
        print
        print 'processing input file %i/%i: %s'%(kFile+1,
                                                 len(args),
                                                 input_file)
        in_file = TFile.Open(input_file,'read')
        ROOT.gDirectory.cd(pwd)
        
        leptonType = options.leptonType    
        
        tree = None
        nEvents_sample = 0    
        specific = None
        treeName = 'Ntuple'
        if not options.allBranches:    
            if leptonType == 'muon':                
                #specific = muonBranches+commonBranches
                mmg = in_file.Get('mmg')
                tree = mmg.Get('final').Get(treeName)
                metaInfoTrees.append(mmg.Get('metaInfo').CloneTree())
                nEvents_sample = mmg.Get('eventCount').GetBinContent(1)
                nEvents_total += mmg.Get('skimCounter').GetBinContent(1)
                mmg = None
            elif leptonType == 'electron':                 
                #specific = electronBranches+commonBranches
                eeg = in_file.Get('eeg')
                tree = eeg.Get('final').Get(treeName)
                metaInfoTrees.append(eeg.Get('metaInfo').CloneTree())
                nEvents_sample = eeg.Get('eventCount').GetBinContent(1)
                nEvents_total += eeg.Get('skimCounter').GetBinContent(1)
                eeg = None
            else:             
                raise Exception('invalid lepton type: %s'%options.leptonType)
                
        total_events = tree.GetEntriesFast()    
        tick_size = total_events/100.0
        if tick_size < 1: tick_size = 1.0
        
        #tm.importTree(treeName,tree,specific)

        
        #tm.cloneTree(treeName,'%s_zs'%treeName,specific)
        #tm.cloneTree(treeName,'%s_zgs'%treeName,specific)
        #tm.cloneTree(treeName,'%s_zgs_nosihih'%treeName,specific)
        
        #setup process dependent stuff
        cuts = setupCuts(options)
        #lepton_mass = lepton_masses[options.leptonType]
        #z_info = z_infos[options.leptonType]
        #lepton_info = lepton_infos[options.leptonType]

        #setup pu-reweighing
        #pu_weight = pu_weight_nominal 
        #if options.isSummer11:
        #    pu_weigt = pu_weight_summer11
        
        procWeight = 1.0
        if options.datType != 'data':
            procWeight = (options.crossSection *
                          run_lumi[options.leptonType][options.runYear]\
                                  [options.runType])

        # setup the corrector (this links the appropriate four momenta
        # into a common naming scheme
        correct = setup_corrections(options.runYear   , options.runType,
                                    options.leptonType, options.datType,
                                    options.leptonCor , options.gamCor,
                                    options.vanilla                       )
        
        ievent = long(0)        
        for event in tree:
            ievent+=1
            #print ievent,total_events,fmod(ievent/total_events,0.01)
            if( not (ievent+1)%int(tick_size) or
                ievent+1 == total_events ):  
                sys.stdout.write('\r%3.0f%s complete! (%i/%i)'%(((ievent+1)/
                                                                 tick_size),
                                                                '%',
                                                                ievent+1,
                                                                total_events))
                sys.stdout.flush()
            
            # setup the common event momentum
            # ell1 = lepton1, ell2 = lepton2
            # gam = photon, Z = dilepton, Zg = Z+photon        
            correct(event)
            
            run_idx = getRunIndex(event.run[0],options.runYear,
                                  options.runType,options.datType,
                                  options.leptonType)
            setattr(event,'procWeight',procWeight)
            setattr(event,'puWeight',1.0)
            if options.datType != 'data':            
                setattr(event,'eventFraction',float(ievent+1)/total_events)
                event.puWeight = pu_S10_CD_reweight(event.nTruePU[0])
                
            #selected_z = []
            #selected_pho_nosihih = []
            #selected_pho = []        
            #bad_leptons = []
            
            if options.datType == 'data':
                # kill run 170722
                # kill the obvious pile up combinatorial event
                if ( event.run[0] == 170722 or
                     (event.run[0]   == 166512 and
                      event.lumi[0] == 1678 and
                      event.evt[0] == 1822682238) ):
                    continue
        
            bestLLG = None
            bestZdiff = -1
            
            for i in range(event.N_PATFinalState):            

                cuts.getCutflow('trigger')(event,i)
                if options.exlProc and not cuts.getCutflow('trigger') :
                    continue        
            
                cuts.getCutflow('pho')(event,i)            
                cuts.getCutflow('leptons')(event,i) 
                if ( options.exlProc and
                     not cuts.getCutflow('leptons') and
                     not cuts.getCutflow('pho') ):
                    continue

                cuts.getCutflow('z')(event,i)
                if options.exlProc and not cuts.getCutflow('z'):
                    continue

                if ( cuts.getCutflow('trigger') and
                     cuts.getCutflow('leptons') and
                     cuts.getCutflow('pho') and
                     cuts.getCutflow('z') ):
                    thisZdiff = abs(Z_POLE-event.Z[i].M())
                    if( cuts.getCut('mindr')[0](event.ell1[i],
                                                event.ell2[i],
                                                event.gam[i]) and
                        (thisZdiff < bestZdiff or bestLLG is None) ):
                        bestZdiff = thisZdiff
                        bestLLG = i
                    
            #event object selection done        
            if options.exlProc and bestLLG is None:
                continue
             
            bestZ = bestLLG
        
            if bestLLG is not None:
                setattr(event,'ell1SF',1.0)
                setattr(event,'ell2SF',1.0)
                #if run_idx != -1:
                #    event.ell1SF = leptonSF_nominal(event.nGoodVtx,
                #                     getattr(event,lepton_info['pt'])[idx1],
                #                    getattr(event,lepton_info['eta'])[idx1],
                #                                    run_idx,
                #                                    options.leptonType)
                #    event.ell2SF = leptonSF_nominal(event.nGoodVtx,
                #                      getattr(event,lepton_info['pt'])[idx2],
                #                     getattr(event,lepton_info['eta'])[idx2],
                #                                    run_idx,
                #                                    options.leptonType)
                setattr(event,'bestZ',bestLLG)
                outTrees.bestZTree(event,tm)
                #tm.fillTree('%s_zs'%treeName,{})
            
            #bestPhoNoSihih = None
            #bestPhoNoSihihPt = -1
            #for idxph in selected_pho_nosihih:
            #    pho.SetPtEtaPhiM(event.phoCorEt[idxph],
            #                     event.phoEta[idxph],
            #                     event.phoPhi[idxph],
            #                     0.0)
            #    if bestPhoNoSihih is None or pho.Pt() > bestPhoNoSihihPt:
            #        if ( bestZ is not None and
            #             cuts.getCut('mindr')[0](event.bestZLeg1,
            #                                     event.bestZLeg2,
            #                                     pho) ):
            #            bestPhoNoSihih = idxph
            #            bestPhoNoSihihPt = pho.Pt()
            #        elif( bestZ is None ):
            #            bestPhoSihih = idxph
            #            bestPhoSihihPt = pho.Pt()
            
            bestPho = bestLLG #and bestPhoNoSihih is None: (below)
            if  options.exlProc and bestPho is None:
                continue

            if bestPho is not None:            
                setattr(event,'phoSF',1.0)
                #if run_idx != -1:
                #    event.phoSF = phoSF_nominal(event.nGoodVtx,
                #                                event.phoEt[bestPho],
                #                                event.phoEta[bestPho],
                #                                run_idx)            
                setattr(event,'bestPho',bestPho)
                
                #if bestPhoNoSihih is not None:            
                #    setattr(event,'phoNoSihihSF',event.phoSF)                
                #    setattr(event,'bestPhoNoSihihIdx',bestPho)
                #    setattr(event,'bestPhoNoSihih',pho)
                #elif bestPhoNoSihih is not None:
                #    pho.SetPtEtaPhiM(event.phoCorEt[bestPhoNoSihih],
                #                     event.phoEta[bestPhoNoSihih],
                #                     event.phoPhi[bestPhoNoSihih],
                #                     0.0)
                #    setattr(event,'phoNoSihihSF',1.0)
                #    if run_idx != -1:
                #        event.phoNoSihihSF = phoSF_nominal(event.nGoodVtx,
                #                                 event.phoEt[bestPhoNoSihih],
                #                                 event.phoEta[bestPhoNoSihih],
                #                                           run_idx)
                #    setattr(event,'bestPhoNoSihihIdx',bestPhoNoSihih)
                #    setattr(event,'bestPhoNoSihih',pho)
        
            if bestLLG is not None:
                #if bestPhoNoSihih is not None:
                #    thezg = event.bestZ + event.bestPhoNoSihih
                #    setattr(event,'bestZGNoSihih',thezg)
                #    outTrees.bestZGTreeNoSihih(event,tm)
                #    tm.fillTree('EventTree_zgs_nosihih',{})
                hzg_r94cat = hzg_4cat_r9based[leptonType](event,bestLLG)
                setattr(event,'bestZG_r94cat',hzg_r94cat)
                hzg_r94cat_mod = \
                               hzg_4cat_r9based_mod[leptonType](event,bestLLG)
                setattr(event,'bestZG_r94cat_mod',hzg_r94cat_mod)
                thezg = event.Zg[bestLLG]            
                selected_events.append((event.run[bestLLG],
                                        event.lumi[bestLLG],
                                        event.evt[bestLLG]))
                setattr(event,'bestZG',thezg)
                outTrees.bestZGTree(event,tm)
                pu_weight_sum += event.puWeight
                #tm.fillTree('%s_zgs'%treeName,{})
            tree = None
        in_file.Close()
        del in_file
        
    #make a nice file name
    input_file = args[0]
    nameparts = input_file[input_file.rfind('/')+1:]
    nameparts = nameparts.split('.')
    
    #output selected event numbers to file if needed
    print
    print 'Selected %i (%.2f) events after processing!'%(len(selected_events),
                                                         pu_weight_sum)

    try:
        os.makedirs(options.prefix)
        print 'Created prefix directory: %s'%options.prefix
    except os.error:
        print 'Prefix directory: %s already exists'%options.prefix
    
    if options.dumpSelectedEvents:
        #sort events
        selected_events.sort(key=lambda event: event[2])
        selected_events.sort(key=lambda event: event[1])
        selected_events.sort(key=lambda event: event[0])
        evf = open(options.prefix +
                   '%s_%s_%s_processed.%s'%('_'.join(nameparts[:-1]),
                                            options.runType,
                                            options.leptonType,
                                            'txt'),
                   'w')
        for ev in selected_events:
            evf.write('Run, Lumi, Event #:\t%i\t%i\t%i\n'%ev)
        evf.close()
        
    #push all of our output trees to a file
    outFileName = ''
    if options.vanilla:
        outFileName = '%s_%s_%s_%s_%s_processed.%s'\
                      %('_'.join(nameparts[:-1]),
                        options.runType,
                        options.datType,
                        options.leptonType,
                        'vanilla',
                        nameparts[-1])
    else:
        outFileName = '%s_%s_%s_%s_%s_%s_processed.%s'\
                      %('_'.join(nameparts[:-1]),
                        options.runType,
                        options.datType,
                        options.leptonType,
                        options.leptonCor,
                        options.gamCor,
                        nameparts[-1])    
    
    hEventCount = TH1I('eventCount','Total Events Processed',1,0,1)
    hEventCount.SetBinContent(1,nEvents_total)
    metaTList = TList()
    for tree in metaInfoTrees:
        metaTList.Add(tree)
    metaTree = TTree.MergeTrees(metaTList)    
    outf = TFile.Open(options.prefix + outFileName,'RECREATE')
    outf.cd()    
    metaTree.Write()    
    hEventCount.Write()
    tm.write()
    outf.Close()
    ROOT.gDirectory.cd(pwd)

cuts_by_year = {2011:{'data':{'muon':{'trigger':muon_triggers_data,
                                      'leptons':mu_cuts_data,
                                      'z':mumu_cuts},
                              'electron':{'trigger':electron_triggers_data,
                                          'leptons':e_cuts_data,
                                          'z':ee_cuts}},
                      'mc':{'muon':{'trigger':muon_triggers_mc,
                                    'leptons':mu_cuts_mc,
                                    'z':mumu_cuts},
                            'electron':{'trigger':electron_triggers_mc,
                                        'leptons':e_cuts_mc,
                                        'z':ee_cuts}},
                      
                      },
                2012:{'data':{'muon':{'trigger':muon_triggers_data,
                                      'leptons':mu_cuts_data_2012,
                                      'z':mumu_cuts},
                              'electron':{'trigger':electron_triggers_data,
                                          'leptons':e_cuts_data_2012,
                                          'z':ee_cuts}},
                      'mc':{'muon':{'trigger':muon_triggers_mc,
                                    'leptons':mu_cuts_mc_2012,
                                    'z':mumu_cuts},
                            'electron':{'trigger':electron_triggers_mc,
                                        'leptons':e_cuts_mc_2012,
                                        'z':ee_cuts}},
                      
                      }
                }
#determine cutflow given input data type
def setupCuts(options):
    datType = options.datType
    leptonType = options.leptonType
    year = options.runYear
    cuts = CompositeCutflow()
    cuts.addCut('mindr',ell_gamma_dr)
    cuts.addCutflow('trigger',
                    cuts_by_year[year][datType][leptonType]['trigger'])
    cuts.addCutflow('leptons',
                    cuts_by_year[year][datType][leptonType]['leptons'])
    cuts.addCutflow('z',
                    cuts_by_year[year][datType][leptonType]['z'])
    
    if datType == 'data':
        cuts.addCutflow('pho',photon_cuts_data)    
    elif options.vetoIFSR:
        cuts.addCutflow('pho',photon_cuts_noifsr)
    else:
        cuts.addCutflow('pho',photon_cuts_mc)
    
    return cuts

#this function returns a run period 
run_prob = hzg_run_probs
def getRunIndex(run,runYear,runType,datType,leptonType):
    if datType == 'data':
        return -1
    else:
       if len(runType) == 1:
           return hzg_run_indices[leptonType][runYear][runType]
       else:
           probs = []
           for key in sorted(hzg_run_probs[leptonType][runYear].keys()):
               probs.append(hzg_run_probs[leptonType][runYear][key])
           max_idx = max(hzg_run_indices[leptonType][runYear].values()) 
           this_idx = 0
           tot_prob = probs[0]
           this_prob = rng.Rndm()
           while ( tot_prob < this_prob and this_idx <= max_idx):
               tot_prob += probs[this_idx]
               this_idx += 1
           return this_idx

parser = ArgumentParser(description='%prog : configurable v\gamma analysis',
                        usage='%prog ++runType={data,A,B,AB} ++leptonType=muon',
                        prefix_chars='-+')

parser.add_argument('++runYear',dest='runYear',
                    type=int,help='dataset year')
parser.add_argument('++runType',#dest='runType',                 
                  type=str,help='run era')
parser.add_argument('++datType',#dest='datType',                 
                  type=str,help='mc or data run')
parser.add_argument('++leptonCor',dest='leptonCor',                 
                  type=str,help='lepton correction name')
parser.add_argument('++photonCor',dest='gamCor',                 
                  type=str,help='photon correction name',
                  default='PHOSPHOR')
parser.add_argument('++leptonType',dest='leptonType',
                  type=str,help='lepton sel.')
parser.add_argument('++exclusiveProcessing',dest='exlProc',
                  action='store_true',default=False,
                  help='stop processing if cut failed')
parser.add_argument('++allBranches',dest='allBranches',
                    action='store_true',
                    default=False,help='store all input branches.')
parser.add_argument('++crossSection',dest='crossSection',
                  type=float,help='MC process cross section, in pb.')
parser.add_argument('++calcCS',dest='calcCS',
                  action='store_true',default=False,help='calculate sigma')
parser.add_argument('++vanilla',dest='vanilla',
                  action='store_true',default=False,
                  help='true off corrections')
parser.add_argument('++dataInput',dest='cs_data_input',
                  type=str,help='the input real data for CS calc')
parser.add_argument('++signalMC',dest='cs_mc_input',
                  type=str,help='the input mc data for CS calc')
parser.add_argument('++vetoIFSR',dest='vetoIFSR',
                    default=False,
                  action='store_true',help='activate I/FSR vetos.')
parser.add_argument('++dumpSelectedEvents',#dest='dumpSelectedEvents',
                  default=False,action='store_true',
                  help='write (run,event,lumi) of selected events to file.')
parser.add_argument('++prefix',dest='prefix',
                  default='./',help='The directory we write output to.')
parser.add_argument('inputdata', nargs='*')


options = parser.parse_args()



if options.runYear is None:
    print 'need to specify run year: 2011, 2012'
    exit(1)
else:
    if options.runYear != 2011 and options.runYear != 2012:
        raise Exception
if options.runType is None:
    if options.runYear == 2011:
        print 'need to specify run type: data, AB'
    elif options.runYear == 2012:
        print 'need to specify run type: data, ABCD'
    else:
        raise Exception('Run year != 2011 or 2012')
    exit(1)
    
if options.leptonType is None:
    print 'need to specify lepton type: electron,muon'
    exit(1)

if options.datType != 'data' and options.crossSection is None:
    print 'need to specify MC process cross section!'
    exit(1)

#set correction types if none set
if options.leptonCor is None:
    if options.leptonType == 'electron':
        options.leptonCor = 'CorrReg'
    elif options.leptonType == 'muon':
        options.leptonCor = 'RochCor'

for k,input in enumerate(options.inputdata):
    if ',' in input:
        temp = input.split(',')
        options.inputdata[k] = temp[0]
        options.inputdata.extend(temp[1:])

print 'Processing: \n\t%s\n\tdatType=%s\n\trunType=%s\n\tleptonType=%s'\
      %('\n\t'.join(options.inputdata),
        options.datType,
        options.runType,
        options.leptonType)
    
if not options.vanilla:
    print '\tActive corrections: lepton=%s photon=%s'%(options.leptonCor,
                                                       options.gamCor)
else:
    print '\tNo lepton or photon corrections in use.'
    
run_analysis(options,options.inputdata)


