/*****************************************************************************
* Project: RooFit *
* Package: RooFitModels *
* @(#)root/roofit:$Id: RooBernstein.cxx 45779 2012-08-31 15:44:51Z moneta $
* Authors: *
* Kyle Cranmer
* *
*****************************************************************************/

//////////////////////////////////////////////////////////////////////////////
//
// BEGIN_HTML
// Bernstein basis polynomials are positive-definite in the range [0,1].
// In this implementation, we extend [0,1] to be the range of the parameter.
// There are n+1 Bernstein basis polynomials of degree n.
// Thus, by providing N coefficients that are positive-definite, there
// is a natural way to have well bahaved polynomail PDFs.
// For any n, the n+1 basis polynomials 'form a partition of unity', eg.
// they sum to one for all values of x. See
// http://www.idav.ucdavis.edu/education/CAGDNotes/Bernstein-Polynomials.pdf
// Step function piece means that for x < value f(x) = 0 and for
// x >= value: f(x) = Gauss(x)RooBernstein
// END_HTML
//

#include "RooFit.h"

#include "Riostream.h"
#include <math.h>
#include "TMath.h"
#include "Math/SpecFunc.h"
#include <UWHiggs/hzg/interface/RooGaussStepBernstein.h>
#include "RooAbsReal.h"
#include "RooRealVar.h"
#include "RooArgList.h"

using namespace std;

ClassImp(RooGaussStepBernstein)

namespace {
  double zeroth(const double x, const double m, const double s, 
		const double a, const double b) {
    const double root2 = std::sqrt(2.0);    
    const double erf_parm_a = (a+m-x)/(root2*s);
    const double erf_parm_b = (b+m-x)/(root2*s);

    return ( std::sqrt(M_PI/2.0)*s*
	     ( std::erf(erf_parm_b) - std::erf(erf_parm_a) ));
  }
  double first(const double x, const double m, const double s,
	       const double a, const double b) {
    const double root2 = std::sqrt(2);
    const double rootpiover2 = std::sqrt(M_PI/2.0);
    const double erf_parm_a = (a+m-x)/(root2*s);
    const double erf_parm_b = (b+m-x)/(root2*s);
    const double gaus_a = std::exp(-0.5*(a+m-x)*(a+m-x)/(s*s));
    const double gaus_b = std::exp(-0.5*(b+m-x)*(b+m-x)/(s*s));
    return ( s*s*(gaus_b-gaus_a) + 
	     rootpiover2*s*(a+m-x)*
	     (std::erf(erf_parm_b)-std::erf(erf_parm_a)) )/(a-b);
  }
  double second(const double x, const double m, const double s,
		const double a, const double b) {
    const double root2 = std::sqrt(2);
    const double amb = std::pow(a-b,2.0);
    const double rootpiover2 = std::sqrt(M_PI/2.0);
    const double erf_a = std::erf((a+m-x)/(root2*s));
    const double erf_b = std::erf((b+m-x)/(root2*s));
    const double gaus_a = std::exp(-0.5*(a+m-x)*(a+m-x)/(s*s));
    const double gaus_b = std::exp(-0.5*(b+m-x)*(b+m-x)/(s*s));
    return s*( gaus_b*s*(2*a-b+m-x) -
	       gaus_a*s*(a+m-x) +
	       rootpiover2*(s*s + (a+m-x)*(a+m-x))*(erf_b - erf_a) )/amb;
  }
  double third(const double x, const double m, const double s,
	       const double a, const double b) {
    const double root2 = std::sqrt(2);
    const double amb   = std::pow(a-b,3.0);
    const double rootpiover2 = std::sqrt(M_PI/2.0);
    const double erf_a = std::erf((a+m-x)/(root2*s));
    const double erf_b = std::erf((b+m-x)/(root2*s));
    const double gaus_a = std::exp(-0.5*(a+m-x)*(a+m-x)/(s*s));
    const double gaus_b = std::exp(-0.5*(b+m-x)*(b+m-x)/(s*s));   
    const double s2 = s*s;
    const double apmmx  = (a+m-x);
    const double apmmx2 = apmmx*apmmx;
    const double poly1 = (3*a*a + b*b + 2*s2 + (m-x)*(m-x) +
			  b*(x-m) - 3*a*(b-m+x));
    const double poly2 = (2*s2 + apmmx2);
    const double poly3 = (3*s2 + apmmx2)*apmmx;
    return s*( gaus_b*s*poly1 -
	       gaus_a*s*poly2 +
	       rootpiover2*poly3*(erf_b - erf_a) )/amb;
  }
  double fourth(const double x, const double m, const double s, 
		const double a, const double b) {
    const double root2 = std::sqrt(2);
    const double amb   = std::pow(a-b,4.0);
    const double rootpiover2 = std::sqrt(M_PI/2.0);
    const double erf_a = std::erf((a+m-x)/(root2*s));
    const double erf_b = std::erf((b+m-x)/(root2*s));
    const double gaus_a = std::exp(-0.5*(a+m-x)*(a+m-x)/(s*s));
    const double gaus_b = std::exp(-0.5*(b+m-x)*(b+m-x)/(s*s));
    
    const double x2 = x*x;
    const double x3 = x*x2;
    const double x4 = x*x3;
    
    const double m2 = m*m;
    const double m3 = m*m2;
    const double m4 = m*m3;
    
    const double a2 = a*a;
    const double a3 = a*a2;
    const double a4 = a*a3;

    const double b2 = b*b;
    const double b3 = b*b2;
    
    const double s2 = s*s;
    const double s3 = s2*s;
    const double s4 = s3*s;

    const double mmx = m-x;
    const double mmx2 = mmx*mmx;
    const double apm = a+m;
    const double apm2 = apm*apm;
    const double apmmx  = (a+m-x);
    const double apmmx2 = apmmx*apmmx;

    const double poly1 = ( -4*a3 + b3 + b*(3*s2 + mmx2) - (5*s2 + mmx2)*mmx -
			   b2*mmx + 6*a2*(b-m+x) - 
			   4*a*(b2 + 2*s2 + mmx2 - b*mmx) );
    const double poly2 = (5*s2 +  apmmx2)*apmmx;
    const double poly3 = ( a4 + 4*a3*m + 6*a2*m2 + 4*a*m3 + m4 +
			   6*a2*s2 + 12*a*m*s2 + 6*m2*s2 + 3*s4 -
			   4*apm*(apm2 + 3*s2)*x + 6*(apm2 + s2)*x2 -
			   4*apm*x3 + x4 );

    return s*( -gaus_b*s*poly1 -
	        gaus_a*s*poly2 +
	       rootpiover2*poly3*(erf_b - erf_a) )/amb;
  }
  double fifth(const double x, const double m, const double s,
	       const double a, const double b) {
    const double root2 = std::sqrt(2);
    const double amb   = std::pow(a-b,5.0);
    const double rootpiover2 = std::sqrt(M_PI/2.0);
    const double erf_a = std::erf((a+m-x)/(root2*s));
    const double erf_b = std::erf((b+m-x)/(root2*s));
    const double gaus_a = std::exp(-0.5*(a+m-x)*(a+m-x)/(s*s));
    const double gaus_b = std::exp(-0.5*(b+m-x)*(b+m-x)/(s*s));
    
    const double x2 = x*x;
    const double x3 = x*x2;
    const double x4 = x*x3;
    
    const double m2 = m*m;
    const double m3 = m*m2;
    const double m4 = m*m3;
    
    const double a2 = a*a;
    const double a3 = a*a2;
    const double a4 = a*a3;

    const double b2 = b*b;
    const double b3 = b*b2;
    const double b4 = b*b3;

    const double s2 = s*s;
    const double s3 = s2*s;
    const double s4 = s3*s;

    const double mmx = m-x;
    const double mmx2 = mmx*mmx;
    const double apm = a+m;
    const double apm2 = apm*apm;
    const double apmmx  = (a+m-x);
    const double apmmx2 = apmmx*apmmx;

    const double poly1 = ( 5*a4 + b4 + b2*(4*s2 + mmx2) +
			   (s2 + mmx2)*(8*s2 + mmx2) - b*(7*s2 + mmx2)*mmx -
			   b3*mmx - 10*a3*(b-m+x) + 
			   10*a2*(b2+2*s2+mmx2-b*mmx) - 
			   5*a*(b3 + b*(3*s2+mmx2) - (5*s2+mmx2)*mmx - b2*mmx) 
			   );
    const double poly2 = (s2 + apmmx2)*(8*s2 + apmmx2);
    const double poly3 = apmmx*( a4 + 4*a3*m + 6*a2*m2 +4*a*m3 + m4 + 
				 10*a2*s2 + 20*a*m*s2 + 10*m2*s2 + 15*s4 -
				 4*apm*(apm2 + 5*s2)*x + 
				 2*(3*apm2 + 5*s2)*x2 - 4*apm*x3 + x4 );

    return s*( gaus_b*s*poly1 -
	        gaus_a*s*poly2 +
	       rootpiover2*poly3*(erf_b - erf_a) )/amb;
  }
  double sixth(const double x, const double m, const double s) {
    const double root2 = std::sqrt(2);
    const double rootpiover2 = std::sqrt(M_PI/2.0);
    const double erf_parm = (m-x)/(root2*s);
    const double gaus = std::exp(-0.5*(m-x)*(m-x)/(s*s));
    
    const double x2 = std::pow(x,2);
    const double x3 = x2*x;
    const double x4 = x3*x;
    const double x5 = x4*x;
    const double x6 = x5*x;

    const double mmx2 = std::pow(m-x,2);
    //const double mmx3 = mmx2*(m-x);
    //const double mmx4 = mmx3*(m-x);
    //const double mmx5 = mmx4*(m-x);

    const double m2 = std::pow(m,2);
    const double m3 = m2*m;
    const double m4 = m3*m;
    const double m5 = m4*m;
    const double m6 = m5*m;

    const double s2 = std::pow(s,2);
    const double s3 = s2*s;
    const double s4 = s3*s;
    const double s5 = s4*s;
    const double s6 = s5*s;
    
    const double poly1 =
      ( (3.0*s2 + mmx2)*(11.0*s2 + mmx2)*(m-x) );
    const double poly2 =
      ( m6 +15.0*m4*s2 + 45.0*m2*s4 + 15.0*s6 - 6.0*m*(m4 + 10.0*m2*s2 + 15.0*s4)*x +
15.0*(m4 + 6.0*m2*s2 +3.0*s4)*x2 - 20.0*m*(m2 + 3.0*s2)*x3 +
15.0*(m2+s2)*x4 - 6.0*m*x5 + x6 );
    const double poly3 =
      ( m6 + 15.0*s6 - 6.0*m5*x + 45.0*s4*x2 + 15.0*s2*x4 + x6 +15.0*m4*(s2 + x2) -
20.0*m3*(3.0*s2*x + x3) +15*m2*(3.0*s4 + 6.0*s2*x2 + x4) -
6.0*m*(15.0*s4*x + 10.0*s2*x3 + x5) );
    return ( s*gaus*( -s*poly1 +
gaus*rootpiover2*(m-x)*poly2 -
gaus*rootpiover2*poly3*std::erf(erf_parm) ) );
  }

  double poly_conv(const double x, const double mean,
		   const double sigma, const double a,
		   const double b, const int i) {
    switch( i ) {
    case 0:
      return zeroth(x,mean,sigma,a,b);
      break;
    case 1:
      return first(x,mean,sigma,a,b);
      break;
    case 2:
      return second(x,mean,sigma,a,b);
      break;
    case 3:
      return third(x,mean,sigma,a,b);
      break;
    case 4:
      return fourth(x,mean,sigma,a,b);
      break;
    case 5:
      return fifth(x,mean,sigma,a,b);
      break;
    case 6:
      return sixth(x,mean,sigma);
      break;
    default:
      assert(1 == 0 && "You requested a convolution that we haven't calculated yet!");
      return -1;
    }
    return -1;
  }
}


//_____________________________________________________________________________
RooGaussStepBernstein::RooGaussStepBernstein()
{
}


//_____________________________________________________________________________
RooGaussStepBernstein::RooGaussStepBernstein(const char* name,
					     const char* title,
					     RooAbsReal& x,
					     RooAbsReal& mean,
					     RooAbsReal& sigma,
					     RooAbsReal& stepVal,
					     const RooArgList& coefList):
  RooAbsPdf(name, title),
  _x("x", "Dependent", this, x),
  _mean("mean","mean of gaussian convolved with polyn",this,mean),
  _sigma("sigma","sigma of gaussian convolved with polyn",this,sigma),
  _stepVal("stepVal","position of the step in absolute scale",this,stepVal),
  _coefList("coefficients","List of coefficients",this)
{
  // Constructor
  TIterator* coefIter = coefList.createIterator() ;
  RooAbsArg* coef ;
  while((coef = (RooAbsArg*)coefIter->Next())) {
    if (!dynamic_cast<RooAbsReal*>(coef)) {
      cout << "RooGaussStepBernstein::ctor(" << GetName()
	   << ") ERROR: coefficient " << coef->GetName()
	   << " is not of type RooAbsReal" << endl ;
      assert(0) ;
    }    
    _coefList.add(*coef) ;
  }
  delete coefIter ;
}



//_____________________________________________________________________________
RooGaussStepBernstein::RooGaussStepBernstein(const RooGaussStepBernstein& other, 
					     const char* name) :
  RooAbsPdf(other, name),
  _x("x", this, other._x),
  _mean("mean",this,other._mean),
  _sigma("sigma",this,other._sigma),
  _stepVal("stepVal",this,other._stepVal),
  _coefList("coefList",this,other._coefList)
{
}


//_____________________________________________________________________________
Double_t RooGaussStepBernstein::evaluate() const
{  
  const Int_t degree = _coefList.getSize() - 1; // n+1 polys of degree n
  RooFIter iter = _coefList.fwdIterator() ;
  
  double poly_vals[degree+1];
  for( int i = 0; i <= degree; ++i ) {
    // we stretch the upper bound by 10% to remove the turn-off of 
    // covolution
    poly_vals[i] = poly_conv(_x,_mean,_sigma,_stepVal,_x.max()*1.10, i);
  }

  double beta = 0.0;
  // iterate through each
  Double_t result = 0.0;
  RooAbsReal* coef = NULL;
  for(Int_t i = 0; i <= degree; ++i) {
    // coef is the bernstein polynomial coefficient
    coef = (RooAbsReal *)iter.next(); 
    // calculate the coefficient in the 'power basis'
    // i.e. the naive polynomial basis
    beta = 0.0;
    for(Int_t k=i; k <= degree; ++k) {      
      beta += (std::pow(-1.,k-i)*
	       TMath::Binomial(degree,k)*
	       TMath::Binomial(k,i)*
	       poly_vals[k]);
    }
    beta *= coef->getVal();     
    result += beta;
  }

  //std::cout << result << std::endl;

  return result;
}


//_____________________________________________________________________________
Int_t RooGaussStepBernstein::getAnalyticalIntegral(RooArgSet& allVars,
						   RooArgSet& analVars,
						   const char* rangeName) const
{
  // No analytical calculation available (yet) of integrals over subranges
  if (rangeName && strlen(rangeName)) {
    return 0 ;
  }
  
  
  if (matchArgs(allVars, analVars, _x)) return 0;
  return 0;
}


//_____________________________________________________________________________
Double_t RooGaussStepBernstein::analyticalIntegral(Int_t code,
const char* rangeName) const
{
  assert(code==1) ;
  return 1.0;
}
