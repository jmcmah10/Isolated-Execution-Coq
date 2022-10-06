Require Import RuntimeDefinitions.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(* Checks if raw_enclave_ID is in the memory range for enclave_state *)
Definition contains_enclave (l: enclave_memory_range) (id: raw_enclave_ID): bool :=
  match (NatMap.find id l) with
  | Some x => true
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

(*
Compute (active_enclave_update (enclave_state_value (enclave_ID_active 0) (cons (emr_mapping 0 (enclave_address_and_data 0 data_none)) nil)) enclave_ID_inactive).
Compute (active_enclave_update (enclave_state_value (enclave_ID_active 0) (cons (emr_mapping 6 (enclave_address_and_data 0 data_none)) nil)) (enclave_ID_active 6)).
Compute (active_enclave_update (enclave_state_value (enclave_ID_active 0) (cons (emr_mapping 0 (enclave_address_and_data 0 data_none)) nil)) (enclave_ID_active 6)).
Compute (active_enclave_update (enclave_state_value (enclave_ID_active 0) ((cons (emr_mapping 0 (enclave_address_and_data 0 data_none)) nil) 
  ++ (cons (emr_mapping 8 (enclave_address_and_data 0 data_none)) nil)
  ++ (cons (emr_mapping 1 (enclave_address_and_data 0 data_none)) nil)
  ++ (cons (emr_mapping 6 (enclave_address_and_data 0 data_none)) nil)
  ++ (cons (emr_mapping 2 (enclave_address_and_data 0 data_none)) nil))) (enclave_ID_active 1)).
*)

(* Enclave Elimination *)
Fixpoint remove_enclave (id: raw_enclave_ID) (l: (list enclave_memory_range_mapping)): enclave_memory_range :=
  match l with
  | nil => nil
  | x :: mem_range =>
    match x with
    | emr_mapping raw_id _ =>
      if eqb raw_id id
      then (remove_enclave id mem_range)
      else x :: (remove_enclave id mem_range)
    end
  end.

Definition enclave_elimination (state: enclave_state) (id: raw_enclave_ID): enclave_state :=
  match state with
  | enclave_state_value e memory_range => enclave_state_value e (remove_enclave id memory_range)
  end.

(*
Compute (enclave_elimination (enclave_state_value (enclave_ID_active 0) (cons (emr_mapping 0 (enclave_address_and_data 0 data_none)) nil)) 6).
Compute (enclave_elimination (enclave_state_value (enclave_ID_active 0) (cons (emr_mapping 6 (enclave_address_and_data 0 data_none)) nil)) 6).
Compute (enclave_elimination (enclave_state_value (enclave_ID_active 0) ((cons (emr_mapping 0 (enclave_address_and_data 0 data_none)) nil) 
  ++ (cons (emr_mapping 6 (enclave_address_and_data 0 data_none)) nil))) 6).
Compute (enclave_elimination (enclave_state_value (enclave_ID_active 0) ((cons (emr_mapping 0 (enclave_address_and_data 0 data_none)) nil) 
  ++ (cons (emr_mapping 8 (enclave_address_and_data 0 data_none)) nil)
  ++ (cons (emr_mapping 1 (enclave_address_and_data 0 data_none)) nil)
  ++ (cons (emr_mapping 6 (enclave_address_and_data 0 data_none)) nil)
  ++ (cons (emr_mapping 2 (enclave_address_and_data 0 data_none)) nil))) 6).
*)