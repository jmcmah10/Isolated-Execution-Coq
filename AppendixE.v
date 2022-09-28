Require Import RuntimeDefinitions.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(* Checks if raw_enclave_ID is in the memory range for enclave_state *)
Fixpoint contains_enclave (l: (list enclave_memory_range_mapping)) (id: raw_enclave_ID): bool :=
  match l with
  | nil => false
  | x :: mem_range =>
    match x with
    | emr_mapping e _ =>
      if eqb e id
      then true
      else contains_enclave mem_range id
    end
  end.

(* Enclave Creation *)
(*
Definition enclave_creation (state: enclave_state) (mu: memory) (e: raw_enclave_ID) (l: memory_address) (n: data): enclave_state :=
*)
  

(* Active Enclave Update *)
Definition active_enclave_update (state: enclave_state) (id: enclave_ID): enclave_state :=
  match state with
  | enclave_state_value e mem_range =>
    match id with
    | enclave_ID_active x =>
      if (contains_enclave mem_range x)
      then enclave_state_value id mem_range
      else state
    | enclave_ID_inactive => enclave_state_value enclave_ID_inactive mem_range
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