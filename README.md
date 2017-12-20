## BLT: Boogie Less Triggers 

<!-- ### Jekyll Themes -->
<!-- Your Pages site will use the layout and styles from the Jekyll
theme you have selected in your
[repository settings](https://github.com/emptylambda/BLT/settings). The
name of this theme is saved in the Jekyll `_config.yml` configuration
file. -->

### What is BLT?
- BLT is a tool that takes programs written in the
  [Boogie IVL](https://www.microsoft.com/en-us/research/project/boogie-an-intermediate-verification-language/)
  and outputs first-order logic conjectures in the
  [TPTP](http://www.cs.miami.edu/~tptp/) syntax, expressing the
  verification conditions. TPTP (stands for Thousands of Problems for
  Theorem Provers) is similar to the default Boogie target language,
  SMTLib, as they are both based on first-order logic and TPTP is
  considered as a widely accepted language standard for automated
  theorem provers. The verification conditions generated by BLT
  utilized some of the recent improvements of TPTP, hence we suggest
  to use BLT together with the [Vampire](https://vprover.github.io)
  theorem prover as its backend (more specifically, our implementation
  is based on the realization of FOOL logic in Vampire). BLT only
  supports a subset of the
  Boogie language at the moment, but we are working on the extension
  of BLT to further support the full language. 

- BLT is accepted by
  [13th International Conference on integrated Formal Methods (iFM 2017)](http://ifm2017.di.unito.it/acceptedPapers.php)
  under the title of "Triggerless Happy: Intermediate Verification
  with a First-Order Prover". 

### Try out BLT
- [OSX Binary](https://github.com/emptylambda/BLT/raw/bdad4168d8868ca87a7ccb92a69d345e1b8af14c/bin/BLT_osx_alpha)
- [Linux x64 Binary](https://github.com/emptylambda/BLT/raw/5d62d16ea11470d024c08e9bec2b2f49304aa517/bin/BLT_unix_001)

### BLT Usage

See the translation in STDOUT:  
`BLT --file=<yourBoogieFile.bpl>`

Or write them into seperate files:  
`BLT --file=<yourBoogieFile.bpl> --tofile=True`

Another option is to enable Tuple encoding:  
`BLT --file=<yourBoogieFile.bpl> --usetuple=True`


### [UPDATE] From THF to TFX
As TPTP recently announced official [update](http://www.cs.miami.edu/~tptp/TPTP/Proposals/TFXTHX.html), we are currently upgrading our syntax accordingly. 


### Contact
Does BLT suit your interest?  Or do you wish to use BLT for other
research? Please feel free drop us a mail anytime!  

