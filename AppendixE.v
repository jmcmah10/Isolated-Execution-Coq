Require Import RuntimeDefinitions.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(* Checks if raw_enclave_ID is in the memory range for enclave_state *)
Definition contains_enclave (l: enclave_memory_range) (id: raw_enclave_ID): bool :=
  match (NatMap.find id l) with
  | Some _ => true
  | None => false
  end.
Inductive validatable_enclave_state :=
  | enclave_state_valid: enclave_state -> validatable_enclave_state
  | enclave_state_error: validatable_enclave_state.

(*
(* Enclave Creation *)
Definition enclave_creation (state: enclave_state) (mu: memory) (e: raw_enclave_ID) (l: memory_address) (n: data): validatable_enclave_state :=
  match state with
  | enclave_state_value _ mem_range =>
    if andb (negb (contains_enclave mem_range e)) (memory_currently_unallocated l n)
    then enclave_state_error
    else enclave_state_error
  end.
*)

(* Active Enclave Update *)
Definition active_enclave_update (state: enclave_state) (id: enclave_ID): validatable_enclave_state :=
  match state with
  | enclave_state_value e mem_range =>
    match id with
    | enclave_ID_active x =>
      match (contains_enclave mem_range x) with
      | true => enclave_state_valid (enclave_state_value id mem_range)
      | false => enclave_state_error
      end
    | enclave_ID_inactive => enclave_state_valid (enclave_state_value enclave_ID_inactive mem_range)
    end
  end.

(* Enclave Elimination *)
Definition enclave_elimination (state: enclave_state) (id: raw_enclave_ID): enclave_state :=
  match state with
  | enclave_state_value e memory_range => enclave_state_value e (NatMap.remove id memory_range)
  end.

(*
Compute (enclave_elimination (enclave_state_value (enclave_ID_inactive) 
  (NatMap.add 1 (enclave_address_and_data (address 0 0) data_none) (NatMap.empty enclave_memory_range_value))) (1)).
Compute (enclave_elimination (enclave_state_value (enclave_ID_inactive) 
  (NatMap.add 2 (enclave_address_and_data (address 0 0) data_none) 
  (NatMap.add 3 (enclave_address_and_data (address 0 0) data_none) 
  (NatMap.add 4 (enclave_address_and_data (address 0 0) data_none) (NatMap.empty enclave_memory_range_value))))) (1)).
Compute (enclave_elimination (enclave_state_value (enclave_ID_inactive) 
  (NatMap.add 2 (enclave_address_and_data (address 0 0) data_none) 
  (NatMap.add 3 (enclave_address_and_data (address 0 0) data_none) 
  (NatMap.add 4 (enclave_address_and_data (address 0 0) data_none) (NatMap.empty enclave_memory_range_value))))) (4)).
*)