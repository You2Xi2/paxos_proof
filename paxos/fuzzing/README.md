# README
This directory fuzzes several specifications of the proof of [the Paxos protocol in Dafny](https://github.com/You2Xi2/paxos_proof), using Z3 library in Python. 

## Table of Contents
- [Acceptor_Protocal](https://github.com/You2Xi2/paxos_proof/tree/main/paxos/fuzzing/Acceptor_Protocol)  
  *Fuzzing of the protocol of Acceptor, with [original Dafny code](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/agents.dfy)*  
  - [AcceptorInit](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorInit.py)  
    The data type of ```Acceptor.Id``` is not specified as Acc in this predicate. 
    Although it doesn't affect the correctness of the whole protocol for requirements in other predicates, it's an useful example with incorrect fuzzing output caught by manual checking. The [fuzzing output](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorInit_output.txt) is wrong in Ln.6 Col.21, as the id of Acceptor should be Acc rather than Ldr. 
  - [AcceptorNext](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorNext.py)
  - [ACceptorPromise](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorPromise.py)  
  

- [Agreement_Chosen_Safety](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety)  
  *Fuzzing of the ```Agreement_Chosen_Safety``` specification in [proof_agreement_invariants.dfy](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/proof_agreement_invariants.dfy)*
  - [Agreement_Chosen_Safety](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Agreement_Chosen_Safety.py)  
  *Directly translation of the predicate*  
  *It's always ```killed``` when running due to the limitation of the Python Z3 library. See the smallest script functioning unexpectedly [here](https://github.com/You2Xi2/paxos_proof/blob/unrealistic_Chosen/paxos/fuzzing/Agreement_Chosen_Safety.py)*  
  - [Agreement_Chosen_Safety_no_exist](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Agreement_Chosen_Safety_no_exist.py)  
    *A simplified version of ```Agreement_Chosen_Safety``` predicate*
    *```Exists``` in ```Chosen``` is removed*
    Its output doesn't meet the requirement of Chosen because of the ```Implies``` in ```Agreement_Chosen_Safety``` predicate. 
    It will generate Empty qrm without Ln.277-282, and qrm with Promise Packet with Ln.277-282, which all conflict with the Chosen requirement.  
  - [Agreement_Chosen_Safety_Fixed_Chosen](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Agreement_Chosen_Safety.py)  
    *A simplified version of ```Agreement_Chosen_Safety``` predicate*
    *```Exists``` in ```Chosen``` and ```Implies``` in ```Agreement_Chosen_Safety``` are removed*
    This version of Agreement_Chosen_Safety can generate fuzzing outputs with Chosen requirement. A sample of over 10 different outputs is [here](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Agreement_Chosen_Safety_output.txt) for your convenience because it gets slower after several iterations. 
  - [Wrong_Agreement_Chosen_Safety_01](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_01.py)  
    *Buggy specification without satisfying output*
    It's buggy because ```Message.val(Packet.msg(S[i])) == v``` in ```AccPacketsHaveValueV``` (Ln.262) is removed.  
    The output says ```The spec is unrealistic in 0 iteration.```  
    However, it's not logical that a missing requirement leads to unrealistic output. Also, it doesn't give many hints for debugging. 
  - [Wrong_Agreement_Chosen_Safety_02](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_02.py)
    *Buggy specification without satisfying output*
    It's buggy because ```Message.is_Accept(Packet.msg(S[i]))``` in ```AccPacketsHaveValueV``` (Ln.261) and ```Message.is_Accept(Packet.msg(p))``` in ```isAcceptPkt``` (Ln.217) are removed.  
    The output says ```The spec is unrealistic in 0 iteration.```  
    However, it's not logical that a missing requirement leads to unrealistic output. Also, it doesn't give many hints for debugging. 
  - [Wrong_Agreement_Chosen_Safety_03](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_03.py)  
    *Buggy specification with incorrect output*
    It's buggy because ```Message.bal(Packet.msg(S[i])) == b``` in ```SetOfAcceptMsgs``` (Ln.243) is removed.  
    [The output](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_03_output.txt) is buggy in 1st iteration because the Ballots in the qrm are not the same in the second iteration.  ```solver.add(Ballot.is_Ballot(Message.bal(Packet.msg(qrm[0]))))```  is needed to give incorrect output in the first few interactions, because the variable is assigned concerning the order of definition of data types. 

- [Validity](https://github.com/You2Xi2/paxos_proof/tree/main/paxos/fuzzing/Validity)  
  *Fuzzing of the ```Validity``` specification in [proof_validity.dfy](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/proof_validity.dfy)*
  - [Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Validity.py)  
  *direct translation of ```Validity``` predicate*
  - [Wrong_Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Wrong_Validity.py)  
  *Buggy specification with incorrect output*
    It's buggy because ```Leader.val(leaders[i]) == v```  (Ln.154) is replaced with ```Leader.ballot(leaders[i]) == b``` (Ln.155) in in ```AllDecidedProcessesDecidesV```.  
    [The output](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Validity_output.txt) is buggy in 2nd iteration because the Value of Decided leaders in leaders (Ln.24, 71) are not the same.  ```ExistDecided``` constraint is needed to give incorrect output in the first few interactions, because the variable is assigned concerning the order of definition of data types. 
  - [Overspecified_Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Overspecified_Validity.py)
  *Buggy specification with correct output*
    It's buggy because ```LeaderState.is_Decided(Leader.state(leaders[i]))```  (Ln.152) is removed in ```AllDecidedProcessesDecidesV```.  
    [The output](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Overspecified_Validity_output.txt) is still correct because the missing constraint in precondition leads to a stronger requirement.   ```ExistDecided``` constraint is needed because the variable is assigned concerning the order of definition of data types. 

## Conclusion 
- Generating fuzzing output is helpful to find under-specified bugs, e.g. [AcceptorInit](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorInit.py), [Wrong_Agreement_Chosen_Safety_03](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_03.py), and [Wrong_Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Wrong_Validity.py). However, sometimes the output doesn't give enough hints to debug, e.g. [Wrong_Agreement_Chosen_Safety_01](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_01.py) and [Wrong_Agreement_Chosen_Safety_02](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Agreement_Chosen_Safety/Wrong_Agreement_Chosen_Safety_02.py). 
- For over-specified bugs, manually constructed expected output that fails to pass the over-specified requirement is helpful, e.g. [Overspecified_Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Overspecified_Validity.py). 
- Python Z3 library is handy to generate fuzzing output, but it has some limitations. 
  - The value of algebra expression data is assigned concerning the order in the datatype definition. This property may avoid it to generate buggy output in the first few iterations.  
  - Programmer should pay additional attention to ```Exists```, ```ForAll```, and ```Implies``` logic. ```Exists``` and  ```ForAll``` may fail to generate output sometimes. `Implies` sometimes doesn't add constrains to the variables. 
