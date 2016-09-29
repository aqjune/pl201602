Require Export D.



Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
intros.
induction n.
eauto.
simpl. SearchAbout (_ + S _). rewrite <- plus_n_Sm. eauto.
Qed.
