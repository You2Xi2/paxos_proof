# README
This directory fuzzes several specifications of the proof of [the Paxos protocol in Dafny](https://github.com/You2Xi2/paxos_proof), using Z3 library in Python. 

## Table of Contents
- [Acceptor_Protocal](https://github.com/You2Xi2/paxos_proof/tree/main/paxos/fuzzing/Acceptor_Protocol) 
  *Fuzzing of the protocol of Acceptor, with [original Dafny code](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/agents.dfy)*  
  - [AcceptorInit](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorInit.py)  
  - [AcceptorNext](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorNext.py)
  - [ACceptorPromise](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Acceptor_Protocol/AcceptorPromise.py)  
- [Agreement_Chosen_Safety](TODO)
  - [Agreement_Chosen_Safety_Fixed_Chosen]()
  - [Agreement_Chosen_Safety_no_exist]()
  - [Agreement_Chosen_Safety]()
  - [Wrong_Agreement_Chosen_Safety_01]()
  - [Wrong_Agreement_Chosen_Safety_02]()
  - [Wrong_Agreement_Chosen_Safety_03]()
- [Validity](https://github.com/You2Xi2/paxos_proof/tree/main/paxos/fuzzing/Validity)  
  - [Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Validity.py)  
  - [Wrong_Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Wrong_Validity.py)  
  - [Overspecified_Validity](https://github.com/You2Xi2/paxos_proof/blob/main/paxos/fuzzing/Validity/Overspecified_Validity.py)
