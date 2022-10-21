def hello := "world"

variable (p q : Prop)

variable (p q r : Prop)

example (h: p -> q) (nq : ¬q) : ¬p :=
  fun hp : p => nq (h hp)

-- Note that (p->q) -> (not q -> not p) is constructive
-- But (not q -> not p) -> (p -> q) is classical



#check Trans
#check And.intro

def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq


example (h : p ∧ q) : q ∧ p :=
  have hp: p := h.left;
  have hq: q := h.right;
  And.intro hq hp






inductive NN where
| zero : NN
| succ : NN -> NN
deriving Repr

open NN

def leftAdd (n : NN) : (NN -> NN) := 
  match n with 
  | NN.zero => fun (m: NN) => m
  | NN.succ n1 => fun (m : NN) => (leftAdd n1 m |> NN.succ)



instance : Add NN where
  add := leftAdd

def leftAddZero (m : NN) : zero + m = m := by rfl;
def leftAddZero1 (m : NN) : m = zero + m := by
  exact Eq.symm (leftAddZero m);
def leftAddSucc (n m : NN) : succ n + m = succ (n +m) := by rfl;

theorem leftAddFromRightByZero (n : NN) : n + NN.zero = n := by 
apply NN.recOn (motive := fun x => x + NN.zero = x);
rfl;
intro a;
intro h1;
calc 
  ((NN.succ a) + NN.zero) = (a + NN.zero |> NN.succ) := rfl
  _ = (a |> NN.succ) := by rw [h1];


theorem leftAddFromRightBySucc (n m:NN): n + (NN.succ m) = ((n + m) |> NN.succ) := by
  apply NN.recOn (motive := fun x => x + (NN.succ m) = ((x + m) |> NN.succ));
  rfl;
  intro a;
  intro h1;
  calc
    ((succ a) + (succ m)) = ((a + (succ m)) |> succ) := rfl
    _ = ((a + m) |> succ |> succ) := by rw [h1]


theorem leftAddCommutative (n m: NN) : n + m = m +n := by 
  apply NN.recOn (motive := fun x => x + m = m + x);
  calc
    zero + m = m  := by rfl
    m = m + zero := by exact leftAddFromRightByZero m |> Eq.symm
  intro a;
  intro h1;
  apply Eq.symm;
  calc
    m + succ a = ((m + a) |> succ) := by exact leftAddFromRightBySucc m a
    _ = ((a + m) |> succ) := by rw [h1]
--    succ a + m = ((a + m) |> succ) := by rfl

theorem leftAddAssociative (a b c: NN) : (a + b) + c = a + (b + c) := by
  apply Eq.symm;
  apply NN.recOn (motive := fun x => x + (b+c) = (x+b) + c);
  rfl;
  intro a;
  intro h1;
  calc
    succ a + (b+c) = succ (a + (b+c)) := rfl
    _ = succ (a + b+ c) := by rw [h1]


theorem succCancellation (a b : NN) : succ a = succ b -> a = b := by
  intro h;
  injection h with h';
  assumption;


theorem succNotZero (a: NN) : ((succ a) ≠ NN.zero) := by
  intro h;
  injection h;
  

theorem leftAddSuccCancellation (a b c: NN) : succ a + b = succ a + c -> a + b = a + c := by
  intro h1;
  exact succCancellation (a+b) (a+c) h1;


theorem A (a b: Prop): a -> (a -> b) -> b := by
  intro a;
  intro h1;
  exact h1 a;


theorem leftAddCancellation (a b c: NN) : a + b = a + c -> b = c := by
  apply NN.recOn (motive := fun a => a + b = a + c -> b = c)
  rw [leftAddZero b]
  rw [leftAddZero c]
  intro h1; exact h1;
  intro a;
  intro h1;
  intro h2;
  exact h1 ((leftAddSuccCancellation a b c) h2);



def isPositive (n : NN) : Prop := 
  n ≠ zero


theorem constructiveContrapositive (p q: Prop) : (p -> q) -> (¬q -> ¬p) := by
  intro h1;
  intro h2;
  exact fun h : p => h2 (h1 h);



theorem sumEqualsZeroImpliesZero (a b : NN) : a + b = zero -> b = zero := by
  cases a with
  | zero => intro h; assumption;
  | succ c => 
    intro h1;
    have h2 : succ c + b = succ (c+b) := leftAddSucc c b;
    rw [h2] at h1;
    have f := succNotZero (c + b) h1;
    exact False.elim f;


theorem addingToPositiveIsPositive (a b: NN) : isPositive b -> isPositive (a + b) := by
  exact constructiveContrapositive (a + b = zero) (b = zero) (sumEqualsZeroImpliesZero a b);


theorem addToZeroImpliesZero (a b: NN) : a + b = zero -> a = zero ∧ b = zero := by
  simp;
  intro p;
  apply And.intro;
  rw [leftAddCommutative] at p;
  exact sumEqualsZeroImpliesZero b a p;
  exact sumEqualsZeroImpliesZero a b p;


theorem reflProducer (t: Sort u) (a: t) : a = a := by
  rfl;

#check Exists.intro

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

theorem positiveImpliesExistenceSuccInverse (a b: NN) : isPositive b -> ∃a, succ a = b := by
  intro h;
  cases b with 
  | zero => exact False.elim (h rfl);
  | succ c => 
  exact Exists.intro c (reflProducer NN (succ c));

def isGTEQThan (m n: NN) : Prop := 
  ∃a:NN,  m = a + n

def isGTThan (m n: NN) : Prop := 
  -- (isGTEQThan m n) ∧ (m ≠ n)
  ∃a:NN,  (m = a + n) ∧ (isPositive a)


theorem reflexivityOfGTEQ (a : NN) : isGTEQThan a a := by
  exact Exists.intro zero (leftAddZero1 a);

#check leftAddAssociative

theorem transitiveOfGTEQ (a b c: NN) 
  (p : isGTEQThan a b) (q : isGTEQThan b c) : isGTEQThan a c := by
  cases p with 
  | intro x1 p => 
  cases q with
  | intro x2 q => 
  rw [q] at p;
  rw [←(leftAddAssociative x1 x2 c)] at p;
  exact Exists.intro (x1 + x2) (p);

#check leftAddZero
#check leftAddCancellation

#check leftAddCommutative
#check addToZeroImpliesZero

theorem leftAddCancellation1 (a b c: NN) (h : b + a = c + a) : b = c := by
   rw [leftAddCommutative, leftAddCommutative c a] at h;
   exact leftAddCancellation a b c h;


theorem antisymmetryOfGTEQ (a b: NN) 
  (p : isGTEQThan a b) (q : isGTEQThan b a) : a = b := by
  cases p with 
  | intro x1 p => 
  cases q with
  | intro x2 q => 
  have h1 := leftAddZero a;
  rw [←h1] at p;
  rw [q] at p;
  rw [←(leftAddAssociative x1 x2 a)] at p;
  have h2 := Eq.symm (leftAddCancellation1 a zero (x1 + x2) p);
  have h3 := addToZeroImpliesZero x1 x2 h2;
  have h4 := h3.right;
  rw [h4] at q;
  have h5 := leftAddZero a;
  rw [h5] at q;
  exact Eq.symm q;

theorem addConstantToBothSides (a b c: NN) (p : a = b) : c + a = c + b := by
  rw [p];


#check leftAddAssociative

theorem additionPreservesGTEQ (a b c :NN) (p : isGTEQThan a b): isGTEQThan (c + a) (c + b) := by
  cases p with 
  | intro x1 p => 
  have h : c + a = x1 + (c + b) := by
    have h1 := (addConstantToBothSides a (x1 + b) c) p;
    rw [leftAddCommutative x1 b, ←leftAddAssociative c b x1, (leftAddCommutative (c + b) x1)] at h1;
    exact h1;
  exact Exists.intro x1 h;

theorem additionPreservesGTEQ1 (a b c :NN) (p : isGTEQThan (c + a) (c + b)): isGTEQThan a b := by
  cases p with
  | intro x1 p => 
  have h1 : a = x1 + b := by sorry;
  exact Exists.intro x1 h1;

theorem notEqualImpliesGT (m n: NN) (p : isGTThan m n) : (isGTEQThan m n) ∧ (m ≠ n) := by 
  -- same witness
  sorry




theorem succGTEQImpliesGT (a b :NN) (p: isGTEQThan b (succ a)) : isGTThan b a := by
  -- same witness
  sorry




theorem trichotomy (a b : NN) : ∃ c, (a = c + b) ∨ (b = c + a) := by
  induction a with
  | zero =>
  have h: b = b + zero := by
    have h1 := leftAddZero1 b;
    rw [leftAddCommutative] at h1;
    exact h1; 
  exact Exists.intro (b) (Or.inr h);
  | succ a h =>
  cases h with
  | intro x1 p =>
  cases p with
  | inl h1 =>
  have q : (succ a) = (succ x1) + b := by sorry;
  exact Exists.intro (succ x1) (Or.inl  q);
  | inr h1 =>
  cases x1 with 
  | zero =>
  have hhh: succ a = (succ zero) + b := by sorry;
  exact Exists.intro (succ zero) (Or.inl hhh);
  | succ x1 =>
  have h2 : b = x1 + succ a := by sorry;
  exact Exists.intro (x1) (Or.inr h2);


theorem GTEQTrichotomy (a b : NN) : (isGTThan a b) ∨ a = b ∨ (isGTThan b a) := by sorry


theorem nothingLessThanZero (m : NN) (p:isGTThan zero m) : False := by sorry

theorem zeroGTEQThanZero (a : NN) (p: isGTEQThan zero a) : a = zero := by sorry

#check nothingLessThanZero
#check False.elim

theorem gtImpliesGTEQSucc {a b :NN} (p: isGTThan (succ b) a) : isGTEQThan b a := by
  -- same witness
  sorry



theorem GTEQImpliesGTOrEqual {m n: NN} (p: isGTEQThan m n) : (isGTThan m n) ∨ (m = n) := by
  sorry


--
-- THIS WAS A FUCKING DISASTER NGL
--  
theorem strongInductionNNBaseZeroPart1 (P : NN -> Prop)
  (q : ∀m : NN, (∀ m': NN, (isGTThan m m') -> (P m')) -> P m)
  : ∀m : NN, (∀ m' : NN, (isGTEQThan m m') -> (P m')) := by
  intro m;
  induction m with
  | zero => 
  intro m1;
  intro h0;
  have h1 : m1 = zero := zeroGTEQThanZero m1 h0;
  have p := q zero;
  --rw [nothingLessThanZero m'] at p;
  have f : (∀ (m' : NN), isGTThan zero m' → P m') := (fun m: NN => 
  (fun p: isGTThan zero m => (False.elim (nothingLessThanZero m p))));
  rw [h1];
  exact p f;
  | succ m2 h1 =>
  have h2 : ∀ (m' : NN), isGTThan (succ m2) m' → P m' := by
    exact (fun m' => (fun x => (h1 m') (gtImpliesGTEQSucc x)));
  --have h3 := q m1;
  intro m1;
  intro h6;
  have h3 := (q (succ m2));
  have h5 := h3 h2;
  --have h5 := 
  have h7 : isGTThan (succ m2) m1 ∨ (succ m2 = m1) := by 
    exact GTEQImpliesGTOrEqual h6;
  cases h7 with
  | inl h8 => exact ((h2 m1) h8);
  | inr h9 => 
    rw [← h9];
    exact h5;




-- In the future lets make this 
-- into a semigroup 
-- and then we can just assert that a diferent base 
-- will be a new semigroup
theorem strongInductionNNBaseZero (P : NN -> Prop)
  (q : ∀m : NN, (∀ m': NN, (isGTThan m m') -> (P m')) -> P m)
  : ∀m : NN, P m := by 
  intro m;
  -- we need to induct with the extra criteria that 
  -- (∀ m': NN, (isGTThan m m') -> (P m'))



  intro m1;
  induction m1 with
  | zero => 
  have p := q zero;
  --rw [nothingLessThanZero m'] at p;
  have f : (∀ (m' : NN), isGTThan zero m' → P m') := (fun m: NN => 
  (fun p: isGTThan zero m => (False.elim (nothingLessThanZero m p))));
  exact p f;
  | succ m1 h1 =>







   
  

