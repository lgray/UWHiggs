#! /usr/bin/env python

import os, sys
from math import sqrt
import time

#analysis_path = '/store/user/lgray/HZG_bias_study'  #for the condor environment

analysis_path = os.path.join(os.environ['hzganalysisroot'],
                             os.environ['hzganalysisname'])

prepend = ''
#prepend = 'root://cmsxrootd.hep.wisc.edu/'

channels = ['muon','electron']

input_mc_samples = ['ZGToLLG-8TeV/ZGToLLG_8TeV-madgraph.Summer12_DR53X-PU_S10_START53_V7A-v1.AODSIM.root',
                    'DYJetsToLL_M-50_TuneZ2Star_8TeV-madgraph-tarball-8TeV/DYJetsToLL_M-50_TuneZ2Star_8TeV-madgraph-tarball.Summer12_DR53X-PU_S10_START53_V7A-v1.AODSIM.root']

study_inputs = {}

for channel in channels:
    base_dir = os.path.join(analysis_path,channel)
    study_inputs[channel] = \
                          [prepend + os.path.join(base_dir,sample) for sample in input_mc_samples]
    


import ROOT
from ROOT import RooWorkspace, RooMCStudy, RooFit, TFile, gDirectory,\
     RooDataSet, RooFormulaVar, RooConstVar, RooArgList, RooArgSet,\
     RooMinuit, RooMinimizer, RooRandom
ROOT.gSystem.Load("libUWHiggshzg.so")
pwd = gDirectory.GetPath()

RooRandom.randomGenerator().SetSeed(int(time.clock()*1e9))

int_lumi = 19.6*1000 #19.6/fb in /pb

def calculate_median(var,dataset):
    vals = []
    for i in xrange(dataset.numEntries()):
        set = dataset.get(i)        
        vals.append(set.getRealValue(var.GetName()))
        del set
    vals.sort()
    middle = len(vals)/2
    return vals[middle]

def prepare_truth_models(ws,cat,mass,channel,turnon,truth):    
    if channel in study_inputs:
        bkg_data = RooDataSet("bkgdata_%s"%(channel),
                              "M_{ll#gamma} with Errors",
                              ws.set("observables_weight"),
                              "weight")
        
        for k,file in enumerate(study_inputs[channel]):
            f_in = TFile.Open(file,"READ")
            gDirectory.cd(pwd)
            n_events = f_in.Get("eventCount").GetBinContent(1)
            tree = f_in.Get("selected_zg").CloneTree()
            tree.SetName("tree_%s_%i"%(channel,k))
            f_in.Close()            
            
            d_in = RooDataSet("temp",
                              "M_{ll#gamma} with Errors",
                              tree,
                              ws.set("observables"))
            norm = RooConstVar("norm","norm",n_events)
            weight = RooFormulaVar("weight",
                                   "weight",
                                   "1.3*@0*@1/@2", #1.3 gives 19.6/fb
                                   RooArgList(ws.var("puWeight"),
                                              ws.var("procWeight"),
                                              norm)
                                   )
            d_in.addColumn(weight)
            d_in_weight = RooDataSet("temp_weight",
                                     "M_{ll#gamma} with Errors",
                                     d_in,
                                     ws.set("observables_weight"),
                                     '','weight')
            bkg_data.append(d_in_weight)
            
        # split off data for each category, create the
        # toy dataset truth models
        data = bkg_data.reduce("Mz + Mzg > 185 && r94cat == %i"%cat)
        getattr(ws,'import')(data,
                             RooFit.Rename('bkgdata_%s_%i'%(channel,
                                                            cat)))
        nevts = data.sumEntries('Mzg > %f && Mzg < %f'%(mass-1.5,mass+1.5))
        #for sigm turn on we want erf truth
        if turnon == 'sigm' and truth == 'exp': 
            #make RooDecay 'truth' model with erf turn on
            ws.factory(
                'RooGaussModel::MzgResoShape_exp_erf_%s_cat%i(Mzg,'\
                'bias_exp_erf_%s_cat%i[120,90,150],sigma_exp_erf_%s_cat%i[1,0.01,10])'%(
                channel,cat,
                channel,cat,
                channel,cat)
                )
            ws.factory(
                'RooDecay::MzgTruthModelBase_exp_erf_%s_cat%i(Mzg,'\
                'tau_erf_%s_cat%i[25,0,50],MzgResoShape_exp_erf_%s_cat%i,'
                'RooDecay::SingleSided)'%(channel,cat,
                                          channel,cat,
                                          channel,cat)
                )            
            ws.factory(
                'RooExtendPdf::MzgTruthModel_exp_erf_%s_cat%i('\
                'MzgTruthModelBase_exp_erf_%s_cat%i,'\
                'norm_truth_exp_%s_cat%i[%f,%f,%f],"ROI")'%(channel,cat,
                                                            channel,cat,
                                                            channel,cat,
                                                            nevts,
                                                            0.25*nevts,1.75*nevts)
                )
            ws.pdf('MzgTruthModel_exp_erf_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit2','scan'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_exp_erf_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit','simplex'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_exp_erf_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.SumW2Error(True)
                )
        if turnon == 'sigm' and truth == 'pow':
            #make power-law truth model with erf turn on
            ws.factory('EXPR::MzgTruthModelShape_pow_erf_%s_cat%i('\
                       '"1e-20 + (@0 > @1)*((@0)^(-@2))",'\
                       '{Mzg,step_pow_erf_%s_cat%i[105,100,130],'\
                       'pow_%s_cat%i[2,0,10]})'\
                       %(channel,cat,
                         channel,cat,
                         channel,cat))
            ws.factory(
                'RooGaussModel::MzgResoShape_pow_erf_%s_cat%i(Mzg,'\
                'bias_pow_erf_%s_cat%i[0],sigma_pow_erf_%s_cat%i[1,0.01,10])'%(
                channel,cat,
                channel,cat,
                channel,cat)
                )
            ws.factory('FCONV::MzgTruthModelBase_pow_erf_%s_cat%i(Mzg,'\
                       'MzgTruthModelShape_pow_erf_%s_cat%i,'\
                       'MzgResoShape_pow_erf_%s_cat%i)'%(channel,cat,
                                                         channel,cat,
                                                         channel,cat))
            ws.factory(
                'RooExtendPdf::MzgTruthModel_pow_erf_%s_cat%i('\
                'MzgTruthModelBase_pow_erf_%s_cat%i,'\
                'norm_truth_pow_erf_%s_cat%i[%f,%f,%f],"ROI")'%(channel,cat,
                                                                channel,cat,
                                                                channel,cat,
                                                                nevts,
                                                                0.25*nevts,1.75*nevts)
                )
            ws.pdf('MzgTruthModel_pow_erf_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit2','scan'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_pow_erf_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit','simplex'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_pow_erf_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.SumW2Error(True)
                )
            
        #for erf fitting turn on we want sigmoid truth
        if turnon == 'erf' and truth == 'exp':
            #build exponential convoluted with sigmoid turn-on
            ws.factory('RooStepExponential::MzgTruthModelShape_exp_sigm_%s_cat%i'\
                       '(Mzg,tau_sigm_%s_cat%i[-0.05,-10,0],'\
                       'step_exp_sigm_%s_cat%i[110,100,130])'%(channel,cat,
                         channel,cat,
                         channel,cat))        
            ws.factory(
                'RooLogistics::MzgResoShape_exp_sigm_%s_cat%i(%s)'%(
                channel,cat,
                ','.join(['Mzg',
                          'bias_exp_sigm_%s_cat%i[0]'%(channel,cat),
                          'sigma_exp_sigm_%s_cat%i[5,0.01,20]'%(channel,cat)])
                )
                )
            ws.factory('FCONV::MzgTruthModelBase_exp_sigm_%s_cat%i(Mzg,'\
                       'MzgTruthModelShape_exp_sigm_%s_cat%i,'\
                       'MzgResoShape_exp_sigm_%s_cat%i)'%(channel,cat,
                                                          channel,cat,
                                                          channel,cat))
            ws.factory(
                'RooExtendPdf::MzgTruthModel_exp_sigm_%s_cat%i('\
                'MzgTruthModelBase_exp_sigm_%s_cat%i,'\
                'norm_truth_exp_sigm_%s_cat%i[%f,%f,%f],"ROI")'%(channel,cat,
                                                                 channel,cat,
                                                                 channel,cat,
                                                                 nevts,
                                                                 0.25*nevts,1.75*nevts)
                )
            ws.pdf('MzgTruthModel_exp_sigm_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit2','scan'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_exp_sigm_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit','simplex'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_exp_sigm_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.SumW2Error(True)
                )
        if turnon == 'erf' and truth == 'pow':
            #build power-law convoluted with sigmoid turn-on
            ws.factory('EXPR::MzgTruthModelShape_pow_sigm_%s_cat%i('\
                       '"1e-20 + (@0 > @1)*((@0)^(-@2))",'\
                       '{Mzg,step_pow_sigm_%s_cat%i[105,100,130],'\
                       'pow_sigm_%s_cat%i[2,0,10]})'\
                       %(channel,cat,
                         channel,cat,
                         channel,cat))        
            ws.factory(
                'RooLogistics::MzgResoShape_pow_sigm_%s_cat%i(%s)'%(
                channel,cat,
                ','.join(['Mzg',
                          'bias_pow_sigm_%s_cat%i[0]'%(channel,cat),
                          'sigma_pow_sigm_%s_cat%i[5,0.01,20]'%(channel,cat)])
                )
                )
            ws.factory('FCONV::MzgTruthModelBase_pow_sigm_%s_cat%i(Mzg,'\
                       'MzgTruthModelShape_pow_sigm_%s_cat%i,'\
                       'MzgResoShape_pow_sigm_%s_cat%i)'%(channel,cat,
                                                          channel,cat,
                                                          channel,cat))
            ws.factory(
                'RooExtendPdf::MzgTruthModel_pow_sigm_%s_cat%i('\
                'MzgTruthModelBase_pow_sigm_%s_cat%i,'\
                'norm_truth_pow_sigm_%s_cat%i[%f,%f,%f],"ROI")'%(channel,cat,
                                                                 channel,cat,
                                                                 channel,cat,
                                                                 nevts,
                                                                 0.25*nevts,1.75*nevts)
                )
            ws.pdf('MzgTruthModel_pow_sigm_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit2','scan'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_pow_sigm_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.Minimizer('Minuit','simplex'),
                RooFit.SumW2Error(False)
                )
            ws.pdf('MzgTruthModel_pow_sigm_%s_cat%i'%(channel,cat)).fitTo(
                ws.data('bkgdata_%s_%i'%(channel,cat)),
                RooFit.SumW2Error(True)
                )        

def build_fitting_models(ws,cat,mass,order,turnon):
    #ws.var('Mzg').setBins(60000,'cache')

    cs=['c%i_cat%i[5,1e-6,30]'%(k+1,cat) for k in range(order)]
    c2s = ['prod::csqr%i_cat%i(c%i_cat%i,c%i_cat%i)'%(k+1,cat,k+1,cat,k+1,cat) for k in range(order)]
    config = ['Mzg',
              'stepVal_cat%i[0.1,0,1.0]'%cat]
    config.append('{c0_cat%[15],'+','.join(c2s)+'}')
    ws.factory(
            'RooStepBernstein::RSBFitModelTruth_cat%i(%s)'%(cat,
                                                            ','.join(config))
            )
    #build standard candle model (RooStepBerntein(x)Gaus)
    if turnon == 'erf':        
        ws.factory(
            "RooGaussStepBernstein::RSBFitModelBase_cat%i(%s)"%(
            cat,
            ','.join(['Mzg',
                      'rsb_bias_cat%i[0]'%cat,
                      'rsb_sigma_cat%i[5,0.01,20]'%(cat),
                      'rsb_stepval_cat%i[115,100,130]'%cat,
                      '{c0_cat%[20],'+','.join(cs)+'}'])
            )
            )
                
        # setup extended pdf with dummy values for norm
        # set proper values during toys loop
        ws.factory(
            'RooExtendPdf::RSBFitModel_cat%i(RSBFitModelBase_cat%i,'\
            'norm_rsb_cat%i[1000,500,1500],"ROI")'%(cat,cat,cat))
    #build alternate fitting model (Bernstein(x)logistics)
    if turnon == 'sigm':
        ws.factory(
            'RooLogistics::RSBFitModelAltReso_cat%i(%s)'%(
            cat,
            ','.join(['Mzg',
                      'rsb_altbias_cat%i[0]'%cat,
                      'rsb_altsigma_cat%i[5,0.01,20]'%cat])
            )
            )
        ws.factory('FCONV::RSBFitModelAltBase_cat%i(Mzg,'\
                   'RSBFitModelTruth_cat%i,'\
                   'RSBFitModelAltReso_cat%i)'%(cat,cat,cat))
        # setup extended pdf with dummy values for norm
        # set proper values during toys loop
        ws.factory(
            'RooExtendPdf::RSBFitModelAlt_cat%i(RSBFitModelAltBase_cat%i,'\
            'norm_altrsb_cat%i[1000,500,1500],"ROI")'%(cat,cat,cat))
    
def gen_data_and_fit(ws, iterations,cat, mass,channel,turnon,truth):
    
    if channel in channels:        

        #fit gaus(x)bern to sigm(x)pow and sigm(x)exp
        #fit sigm(x)bern to erf(x)pow and erf(x)exp
        
        n_sample = int(ws.data('bkgdata_%s_%i'%(channel,cat)).sumEntries())
        if turnon == 'erf' and truth == 'exp':
            ws.factory('pull_ROI_erf_on_sigmexp_%s_cat%i[0]'%(channel,cat))
            ws.defineSet('biasVars_%s_cat%i'%(channel,cat),
                         'pull_ROI_erf_on_sigmexp_%s_cat%i,'%(channel,cat))
        if turnon == 'erf' and truth == 'pow':
            ws.factory('pull_ROI_erf_on_sigmpow_%s_cat%i[0]'%(channel,cat))
            ws.defineSet('biasVars_%s_cat%i'%(channel,cat),
                         'pull_ROI_erf_on_sigmpow_%s_cat%i,'%(channel,cat)
                         )
            
        if turnon == 'sigm' and truth == 'exp':        
            ws.factory('pull_ROI_sigm_on_erfexp_%s_cat%i[0]'%(channel,cat))
            ws.defineSet('biasVars_%s_cat%i'%(channel,cat),                         
                         'pull_ROI_sigm_on_erfexp_%s_cat%i,'%(channel,cat)
                         )
        if turnon == 'sigm' and truth == 'pow':
            ws.factory('pull_ROI_sigm_on_erfpow_%s_cat%i[0]'%(channel,cat))
            ws.defineSet('biasVars_%s_cat%i'%(channel,cat), 
                         'pull_ROI_sigm_on_erfpow_%s_cat%i'%(channel,cat)
                         )
        biasData = RooDataSet('biasData_%s_cat%i'%(channel,cat),
                              'bias data',
                              ws.set('biasVars_%s_cat%i'%(channel,cat)))
        
        for i in xrange(iterations):

            ### SIGM            
            #build ERF toy data to fit with SIGM
            if turnon == 'sigm' and truth == 'exp':
                truth_exp_erf = ws.pdf('MzgTruthModel_exp_erf_%s_cat%i'%(channel,cat))
                toy_data_exp_erf = truth_exp_erf.generate(                    
                    RooArgSet(ws.var('Mzg')),
                    n_sample,
                    RooFit.Extended(),
                    RooFit.Name('toy_erfexp_%s_cat%i_%i'%(channel,cat,i))
                    )
                true_ROI_yield_erfexp = ws.var('norm_truth_exp_%s_cat%i'%(channel,cat)).getVal()

                #fit logistics(x)bern to erfexp
                ws.var('norm_altrsb_cat%i'%cat).setMin(true_ROI_yield_erfexp*0.25)
                ws.var('norm_altrsb_cat%i'%cat).setMax(true_ROI_yield_erfexp*1.75)
                ws.var('norm_altrsb_cat%i'%cat).setVal(true_ROI_yield_erfexp)            
                
                minos_var = RooArgSet(ws.var('norm_altrsb_cat%i'%cat))
                sigm_nll = ws.pdf('RSBFitModelAlt_cat%i'%cat).createNLL(
                    toy_data_exp_erf
                    )
                sigm_min = RooMinimizer(sigm_nll)
                sigm_min.setPrintLevel(1)
                sigm_min.minimize('Minuit2','scan')
                sigm_min.minimize('Minuit2','simplex')                
                migrad_out = sigm_min.migrad()                
                migrad_out = sigm_min.migrad()
                hesse_out  = sigm_min.hesse()
                
                fit_sigm_norm = ws.var('norm_altrsb_cat%i'%cat).getVal()
                fit_sigm_err  = ws.var('norm_altrsb_cat%i'%cat).getError()
                fit_sigm_pull = (fit_sigm_norm - true_ROI_yield_erfexp)/fit_sigm_err

                #if fit failed run minos
                if migrad_out != 0 or hesse_out != 0:
                    migrad_out = sigm_min.migrad()                    
                    if migrad_out != 0:
                        sigm_min.minos(minos_var)
                        fit_sigm_err  = max(abs(ws.var('norm_altrsb_cat%i'%cat).getErrorHi()),
                                            abs(ws.var('norm_altrsb_cat%i'%cat).getErrorLo()))
                    else:
                        fit_sigm_err  = ws.var('norm_altrsb_cat%i'%cat).getError()
                    fit_sigm_norm = ws.var('norm_altrsb_cat%i'%cat).getVal()
                    fit_sigm_pull = (fit_sigm_norm - true_ROI_yield_erfexp)/fit_sigm_err
                
                print i, fit_sigm_norm, fit_sigm_err, true_ROI_yield_erfexp, fit_sigm_pull
                
                ws.var('pull_ROI_sigm_on_erfexp_%s_cat%i'%(channel,cat)).setVal(
                    fit_sigm_pull
                    )                

                biasData.add(ws.set('biasVars_%s_cat%i'%(channel,cat)))

                var = ws.var('pull_ROI_sigm_on_erfexp_%s_cat%i'%(channel,cat))

                print 'cumulative median bias: %.3f'%calculate_median(var,biasData)
                
                var = None                

                del sigm_min
                del sigm_nll
                del truth_exp_erf

            if turnon =='sigm' and truth =='pow':
                truth_pow_erf = ws.pdf('MzgTruthModel_pow_erf_%s_cat%i'%(channel,cat))                
                toy_data_pow_erf = truth_pow_erf.generate(                    
                    RooArgSet(ws.var('Mzg')),
                    n_sample,
                    RooFit.Extended(),
                    RooFit.Name('toy_erfpow_%s_cat%i_%i'%(channel,cat,i))
                    )
                
                true_ROI_yield_erfpow = ws.var('norm_truth_pow_erf_%s_cat%i'%(channel,cat)).getVal()
                               
                #fit logistics(x)bern to erfpow
                ws.var('norm_altrsb_cat%i'%cat).setMin(true_ROI_yield_erfpow*0.25)
                ws.var('norm_altrsb_cat%i'%cat).setMax(true_ROI_yield_erfpow*1.75)
                ws.var('norm_altrsb_cat%i'%cat).setVal(true_ROI_yield_erfpow)
                
                minos_var = RooArgSet(ws.var('norm_altrsb_cat%i'%cat))
                sigm_nll = ws.pdf('RSBFitModelAlt_cat%i'%cat).createNLL(
                    toy_data_pow_erf
                    )
                sigm_min = RooMinimizer(sigm_nll)
                sigm_min.setPrintLevel(1)
                sigm_min.minimize('Minuit2','scan')
                sigm_min.minimize('Minuit2','simplex')
                migrad_out = sigm_min.migrad()                
                migrad_out = sigm_min.migrad()
                hesse_out  = sigm_min.hesse()                

                fit_sigm_norm = ws.var('norm_altrsb_cat%i'%cat).getVal()
                fit_sigm_err  = ws.var('norm_altrsb_cat%i'%cat).getError()
                fit_sigm_pull = (fit_sigm_norm - true_ROI_yield_erfpow)/fit_sigm_err

                #if fit failed run minos
                if migrad_out != 0 or hesse_out != 0:
                    migrad_out = sigm_min.migrad()                    
                    if migrad_out != 0:
                        sigm_min.minos(minos_var)
                        fit_sigm_err  = max(abs(ws.var('norm_altrsb_cat%i'%cat).getErrorHi()),
                                           abs(ws.var('norm_altrsb_cat%i'%cat).getErrorLo()))
                    else:
                        fit_sigm_err  = ws.var('norm_altrsb_cat%i'%cat).getError()
                    fit_sigm_norm = ws.var('norm_altrsb_cat%i'%cat).getVal()
                    fit_sigm_pull = (fit_sigm_norm - true_ROI_yield_erfpow)/fit_sigm_err
                
                ws.var('pull_ROI_sigm_on_erfpow_%s_cat%i'%(channel,cat)).setVal(
                    fit_sigm_pull
                    )

                print i, fit_sigm_norm, fit_sigm_err, true_ROI_yield_erfpow, fit_sigm_pull

                biasData.add(ws.set('biasVars_%s_cat%i'%(channel,cat)))
                
                var = ws.var('pull_ROI_sigm_on_erfpow_%s_cat%i'%(channel,cat))

                print 'cumulative median bias: %.3f'%calculate_median(var,biasData)
                
                var = None
                                
                del sigm_min
                del sigm_nll                
                del truth_pow_erf
            
            ##### ERF
            # generate SIGM data to fit with ERF
            #### fit erf(x)bern models  
            if turnon == 'erf' and truth == 'exp':
                truth_exp_sigm = ws.pdf('MzgTruthModel_exp_sigm_%s_cat%i'%(channel,cat))
                toy_data_exp_sigm = truth_exp_sigm.generate(                    
                    RooArgSet(ws.var('Mzg')),
                    n_sample,
                    RooFit.Extended(),
                    RooFit.Name('toy_sigmexp_%s_cat%i_%i'%(channel,cat,i))
                    )
                true_ROI_yield_sigmexp = ws.var('norm_truth_exp_sigm_%s_cat%i'%(channel,cat)).getVal()

                #fit erf(x)bern to sigmexp
                ws.var('norm_rsb_cat%i'%cat).setMin(true_ROI_yield_sigmexp*0.25)
                ws.var('norm_rsb_cat%i'%cat).setMax(true_ROI_yield_sigmexp*1.75)
                ws.var('norm_rsb_cat%i'%cat).setVal(true_ROI_yield_sigmexp)
                
                minos_var = RooArgSet(ws.var('norm_rsb_cat%i'%cat))
                gaus_nll = ws.pdf('RSBFitModel_cat%i'%cat).createNLL(
                    toy_data_exp_sigm
                    )
                gaus_min= RooMinimizer(gaus_nll)
                gaus_min.setPrintLevel(1)
                gaus_min.minimize('Minuit2','scan')
                gaus_min.minimize('Minuit2','simplex')
                migrad_out = gaus_min.migrad()                
                migrad_out = gaus_min.migrad()
                hesse_out  = gaus_min.hesse()
                
                #get parabolic errors regardless
                fit_erf_norm = ws.var('norm_rsb_cat%i'%cat).getVal()
                fit_erf_err  = ws.var('norm_rsb_cat%i'%cat).getError()
                fit_erf_pull = (fit_erf_norm - true_ROI_yield_sigmexp)/fit_erf_err

                #if fit failed run minos
                if migrad_out != 0 or hesse_out != 0:
                    migrad_out = gaus_min.migrad()                      
                    if  migrad_out != 0:
                        gaus_min.minos(minos_var)                        
                        fit_erf_err  = max(abs(ws.var('norm_rsb_cat%i'%cat).getErrorHi()),
                                           abs(ws.var('norm_rsb_cat%i'%cat).getErrorLo()))
                    else:                        
                        fit_erf_err = ws.var('norm_rsb_cat%i'%cat).getError()
                    fit_erf_norm = ws.var('norm_rsb_cat%i'%cat).getVal()
                    fit_erf_pull = (fit_erf_norm - true_ROI_yield_sigmexp)/fit_erf_err
                
                ws.var('pull_ROI_erf_on_sigmexp_%s_cat%i'%(channel,cat)).setVal(
                    fit_erf_pull
                    )
                print i,fit_erf_norm, fit_erf_err, true_ROI_yield_sigmexp, fit_erf_pull

                biasData.add(ws.set('biasVars_%s_cat%i'%(channel,cat)))

                var = ws.var('pull_ROI_erf_on_sigmerf_%s_cat%i'%(channel,cat))

                print 'cumulative median bias: %.3f'%calculate_median(var,biasData)
                
                var = None
                
                del gaus_min
                del gaus_nll    
                del truth_exp_sigm
                
            if turnon == 'erf' and truth == 'pow':
                truth_pow_sigm = ws.pdf('MzgTruthModel_pow_sigm_%s_cat%i'%(channel,cat))
                
                toy_data_pow_sigm = truth_pow_sigm.generate(                    
                    RooArgSet(ws.var('Mzg')),
                    n_sample,
                    RooFit.Extended(),
                    RooFit.Name('toy_sigmpow_%s_cat%i_%i'%(channel,cat,i))
                    )            
                true_ROI_yield_sigmpow = ws.var('norm_truth_pow_sigm_%s_cat%i'%(channel,cat)).getVal()

                #fit erf(x)bern to sigmpow
                ws.var('norm_rsb_cat%i'%cat).setMin(true_ROI_yield_sigmpow*0.25)
                ws.var('norm_rsb_cat%i'%cat).setMax(true_ROI_yield_sigmpow*1.75)
                ws.var('norm_rsb_cat%i'%cat).setVal(true_ROI_yield_sigmpow)
                
                minos_var = RooArgSet(ws.var('norm_rsb_cat%i'%cat))
                gaus_nll = ws.pdf('RSBFitModel_cat%i'%cat).createNLL(
                    toy_data_pow_sigm
                    )
                gaus_min= RooMinimizer(gaus_nll)
                gaus_min.setPrintLevel(1)
                gaus_min.minimize('Minuit2','scan')
                gaus_min.minimize('Minuit2','simplex')
                migrad_out = gaus_min.migrad()                
                migrad_out = gaus_min.migrad()
                hesse_out  = gaus_min.hesse()                                     
            
                fit_erf_norm = ws.var('norm_rsb_cat%i'%cat).getVal()
                fit_erf_err  = ws.var('norm_rsb_cat%i'%cat).getError()
                fit_erf_pull = (fit_erf_norm - true_ROI_yield_sigmpow)/fit_erf_err

                #if fit failed run minos
                if migrad_out != 0 or hesse_out != 0:
                    migrad_out = gaus_min.migrad()                    
                    if migrad_out != 0:
                        gaus_min.minos(minos_var)
                        fit_erf_err  = max(abs(ws.var('norm_rsb_cat%i'%cat).getErrorHi()),
                                           abs(ws.var('norm_rsb_cat%i'%cat).getErrorLo()))
                    else:
                        fit_erf_err  = ws.var('norm_rsb_cat%i'%cat).getError()
                    fit_erf_norm = ws.var('norm_rsb_cat%i'%cat).getVal()
                    fit_erf_pull = (fit_erf_norm - true_ROI_yield_sigmpow)/fit_erf_err        
                

                print i, fit_erf_norm, fit_erf_err, true_ROI_yield_sigmpow, fit_erf_pull
                
                ws.var('pull_ROI_erf_on_sigmpow_%s_cat%i'%(channel,cat)).setVal(
                    fit_erf_pull
                    )
                
                biasData.add(ws.set('biasVars_%s_cat%i'%(channel,cat)))

                var = ws.var('pull_ROI_erf_on_sigmpow_%s_cat%i'%(channel,cat))

                print 'cumulative median bias: %.3f'%calculate_median(var,biasData)
                
                var = None
                
                #getattr(ws,'import')(toy_data_exp_sigm)
                #getattr(ws,'import')(toy_data_pow_sigm)
                
                del gaus_min
                del gaus_nll   
                del truth_pow_sigm
            
        getattr(ws,'import')(biasData)

# if being executed run bias study
if __name__ == '__main__':
    ntoys = int(sys.argv[1])    
    category = int(sys.argv[2])
    mass = float(sys.argv[3])
    channel = sys.argv[4]
    order = int(sys.argv[5])
    turnon = sys.argv[6] #fitted turn on type!!!
    truth = sys.argv[7] #truth model type!!!
    
    bs = RooWorkspace('bias_study')

    bs.factory("procWeight[0]")
    bs.factory("puWeight[0]")
    bs.factory("weight[0]")
    bs.factory("Mzg[100,180]")
    bs.var("Mzg").setRange("ROI",mass-1.5,mass+1.5)
    bs.var("Mzg").setBins(40000,"cache")
    bs.factory("Mz[0]")
    #bs.factory("dMzg[0,25]")
    #bs.factory("dMz[0,25]")
    bs.factory("r94cat[cat1=1,cat2=2,cat3=3,cat4=4]")
    bs.defineSet("observables",
                 "Mzg,Mz,r94cat,procWeight,puWeight")
    bs.defineSet("observables_weight",
                 "Mzg,Mz,r94cat,procWeight,puWeight,weight")

    prepare_truth_models(bs,category,mass,channel,turnon,truth)
    
    build_fitting_models(bs,category,mass,order,turnon)

    gen_data_and_fit(bs, ntoys, category,mass,channel,turnon,truth)

    out_f = TFile.Open("bias_study_%s_%s_%s_ntoys%i_cat%i_m%s_order%i.root"%(channel,turnon,truth,ntoys,
                                                                             category,
                                                                             str(mass).replace('.','p'),
                                                                             order),
                       "recreate")
    bs.Write()
    out_f.Close()
