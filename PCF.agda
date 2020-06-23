module PCF where


data Type : Set where
  nat : Type
  _=>_ : Type -> Type -> Type


data Con : Set where
  ∙ : Con
  _,_ : Con -> Type -> Con

data _∈_ (A : Type) : Con -> Set where
  vz : ∀ {Γ} -> A ∈ (Γ , A)
  vs : ∀ {Γ} {B} -> A ∈ Γ -> A ∈ (Γ , B)


data Term (Γ : Con) : Type -> Set where
  zero : Term Γ nat
  succ : Term Γ nat -> Term Γ nat
  pred : Term Γ nat -> Term Γ nat
  lam  : ∀ {A B} -> Term (Γ , A) B -> Term Γ (A => B)
  var  : ∀ {A} -> A ∈ Γ -> Term Γ A
  app  : ∀ {A B} -> Term Γ (A => B) -> Term Γ A -> Term Γ B
  fix  : ∀ {A} -> Term Γ (A => A) -> Term Γ A
  ifz  : ∀ {A} -> Term Γ nat -> Term Γ A -> Term Γ A -> Term Γ A

  
data Value (Γ : Con) : Type -> Set where
  zero : Value Γ nat
  succ : Value Γ nat -> Value Γ nat
  pred : Value Γ nat -> Value Γ nat
  lam  : ∀ {A B} -> Value (Γ , A) B -> Value Γ (A => B)
  

data Neutral (Γ : Con) : Type -> Set where
  var : ∀ {A} -> A ∈ Γ -> Neutral Γ A
  app : ∀ {A B} -> Neutral Γ (A => B) -> Value Γ A -> Neutral Γ B
  ifz : ∀ {A} -> Neutral Γ nat -> Value Γ A -> Value Γ A -> Neutral Γ A
  fix : ∀ {A} -> Neutral Γ (A => A) -> Neutral Γ A



  
  
  

