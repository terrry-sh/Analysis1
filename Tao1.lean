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

   
  

