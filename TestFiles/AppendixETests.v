Require Import RuntimeDefinitions.
Require Import AppendixE.

Definition mem_range := (NatMap.add 1 (enclave_address_and_data (address 3 0) 0) (NatMap.add 3 (enclave_address_and_data (address 2 0) 0) (NatMap.add 5 (enclave_address_and_data (address 0 0) 0) (NatMap.empty enclave_memory_range_value)))).
Definition E := enclave_state_value (enclave_ID_active 3) mem_range.
Definition D0 := (NatMap.add 0 (data_value 0) (NatMap.add 1 (data_value 0) (NatMap.add 2 (data_value 0) (NatMap.add 3 (data_value 0) (NatMap.empty data))))).
Definition D1 := (NatMap.add 0 (data_value 0) (NatMap.add 1 (data_value 1) (NatMap.add 2 (data_value 0) (NatMap.add 3 (data_value 0) (NatMap.empty data))))).
Definition mu := (NatMap.add 0 D0 (NatMap.add 1 D1 (NatMap.add 2 D1 (NatMap.add 3 D0 (NatMap.empty data_block))))).


(* Enclave Creation *)
(* PASS *)
Compute (enclave_creation E mu 2 (address 0 0) 4).
Compute (enclave_creation E mu 2 (address 0 0) 5).
Compute (enclave_creation E mu 2 (address 1 2) 3).
Compute (enclave_creation E mu 2 (address 0 0) 0).
Compute (enclave_creation E mu 2 (address 1 1) 0).
(* FAIL *)
Compute (enclave_creation E mu 2 (address 0 0) 6).
Compute (enclave_creation E mu 3 (address 3 0) 4).
Compute (enclave_creation E mu 2 (address 1 2) 4).



(* Active Enclave Update *)
(* PASS *)
Compute (active_enclave_update E enclave_ID_inactive).
Compute (active_enclave_update E (enclave_ID_active 1)).
(* FAIL *)
Compute (active_enclave_update E (enclave_ID_active 2)).


(* Enclave Elimination *)
Compute (enclave_elimination (enclave_state_value (enclave_ID_inactive) 
  (NatMap.add 1 (enclave_address_and_data (address 0 0) 5) (NatMap.empty enclave_memory_range_value))) (1)).
Compute (enclave_elimination (enclave_state_value (enclave_ID_inactive) 
  (NatMap.add 2 (enclave_address_and_data (address 0 0) 3) 
  (NatMap.add 3 (enclave_address_and_data (address 0 0) 7) 
  (NatMap.add 4 (enclave_address_and_data (address 0 0) 11) (NatMap.empty enclave_memory_range_value))))) (1)).
Compute (enclave_elimination (enclave_state_value (enclave_ID_inactive) 
  (NatMap.add 2 (enclave_address_and_data (address 0 0) 3) 
  (NatMap.add 3 (enclave_address_and_data (address 0 0) 7) 
  (NatMap.add 4 (enclave_address_and_data (address 0 0) 11) (NatMap.empty enclave_memory_range_value))))) (4)).