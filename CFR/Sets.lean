namespace CFR

structure Set (α : Type) where
  pred : α → Prop
deriving Inhabited

-- Operações interessantes
def Mem : α → Set α → Prop := fun a A => A.pred a
infix:50 " ∈ " => Mem

def Nem : α → Set α → Prop := fun a A => ¬(a ∈ A)
infix:50 " ∉ " => Nem

def Inter (X Y : Set α): Set α := {pred := fun a => a ∈ X ∧ a ∈ Y}
infix:60 " ∩ " => Inter

def Union (X Y : Set α): Set α := {pred := fun a => a ∈ X ∨ a ∈ Y}
infix:60 " ∪ " => Union

def Diff (X Y : Set α): Set α := {pred := fun a => a ∈ X ∧ a ∉ Y}
infix:65 "//" => Diff

def Sub (X Y : Set α): Prop := ∀ a, a ∈ X → a ∈ Y
infix:55 " ⊆ " => Sub

def Sup (X Y : Set α): Prop := ∀ a, a ∈ Y → a ∈ X
infix:55 " ⊇ " => Sup

def Power (X : Set α): Set (Set α) := {pred := fun Y => Y ⊆ X}
prefix:100 "𝒫" => Power

def BigInter (X : Set (Set α)): Set α := {pred := fun a => ∀ x, x ∈ X → a ∈ x}
prefix:100 "⋂" => BigInter

def BigUnion (X : Set (Set α)): Set α := {pred := fun a => ∃ x, x ∈ X ∧ a ∈ x}
prefix:100 "⋃" => BigUnion

-- Obs: SingleInsert a X ≝ X ∪ {a}
def Insert {α : Type} (a' : α) (X : Set α) : Set α := {pred := fun a => a = a' ∨ a ∈ X}

-- SetBuilder
def Builder {α : Type} (p : α → Prop) : Set α := {pred := p}
notation "{ " x " | " p " }" => Builder (fun x => p)
#check 6 ∈ {x | x > 5}

-- Conjuntos importantes
def Empty : Set α := {pred := fun _ => False}
notation "∅" => Empty

def Univ : Set α := {pred := fun _ => True}
notation "U" => Univ

def Singleton (a : α) : Set α := Insert a ∅
notation "{"a"}" => Singleton a

def Inhabited (A : Set α) : Prop := ∃ a, a ∈ A
notation A " habitado" => Inhabited A

-- Teoremas interessantes

theorem set_ext_pred (X Y : Set α): X = Y ↔ X.pred = Y.pred := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    let ⟨p_X⟩ := X
    let ⟨p_Y⟩ := Y
    exact congrArg Set.mk h

theorem set_ext (X Y : Set α): X = Y ↔ ∀ a, a ∈ X ↔ a ∈ Y := by
  apply Iff.intro
  · intro h
    rw [h]
    intro a
    apply Iff.intro <;> exact fun h => h
  · intro h
    rw [set_ext_pred]
    funext a
    exact propext (h a)

theorem double_inclusion : X = Y ↔ X ⊇ Y ∧ Y ⊇ X := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro a h₁
      rw [← h] at h₁
      exact h₁
    · intro a h₁
      rw [h] at h₁
      exact h₁
  · rintro ⟨h₁, h₂⟩
    rw [set_ext]
    intro a
    apply Iff.intro
    · apply h₂ a
    · apply h₁ a

theorem empty_nin : ∀ a : α, a ∉ ∅ := fun _ h => False.elim h

theorem sup_inv_sub : X ⊇ Y ↔ Y ⊆ X := by
  apply Iff.intro <;> intro h a h₁ <;> exact (h a) h₁

theorem subp_refl : X ⊆ X ∧ X ⊇ X := by
  apply And.intro <;> intro a h <;> exact h

theorem sub_trans : X ⊆ Y ∧ Y ⊆ Z → X ⊆ Z := by
  rintro ⟨h₁ , h₂⟩
  intro a h
  apply h₂ a
  apply h₁ a
  exact h

theorem sup_trans : X ⊇ Y ∧ Y ⊇ Z → X ⊇ Z := by
  rintro ⟨h₁, h₂⟩
  rw [sup_inv_sub] at *
  exact sub_trans ⟨h₂, h₁⟩

theorem subp_eq: X = Y → X ⊇ Y ∧ X ⊆ Y := by
  intro h
  rw [←h]
  apply And.intro <;> apply subp_refl.1

theorem unique_empty (h : ∀ a, a ∉ X) : X = ∅ := by
  rw [double_inclusion]
  apply And.intro <;> intro a h₁
  · contradiction
  · apply h a h₁

theorem sub_left_union : X ⊆ X ∪ Y := by
  intro a h
  apply Or.inl h

theorem sub_right_of_union : Y ⊆ X ∪ Y := by
  intro a h
  exact Or.inr h

theorem inter_sub_left : X ∩ Y ⊆ X := by
  intro a h
  exact And.left h

theorem inter_sub_right : X ∩ Y ⊆ Y := by
  intro a h
  exact And.right h

theorem diff_sub : X // Y ⊆ X := fun _ h => And.left h


theorem mem_union (h : a ∈ X) : ∀ Y, a ∈ X ∪ Y ∧ a ∈ Y ∪ X := by
  intro Y
  apply And.intro
  · apply Or.inl h
  · apply Or.inr h

theorem id_union : ∅ ∪ X = X ∧ X ∪ ∅ = X := by
  apply And.intro
  <;> apply double_inclusion.mpr
  <;> apply And.intro
  <;> intro a h
  <;> try apply Or.elim h
  <;> try exact fun h₁ => h₁
  · apply Or.inr h
  · exact fun h₁ => False.elim h₁
  · apply Or.inl h
  · exact fun h₁ => False.elim h₁

theorem idempotente_union : X ∪ X = X := by
  apply double_inclusion.mpr
  apply And.intro <;> intro a h
  · apply Or.inl h
  · apply Or.elim h <;> exact fun h => h

theorem id_inter : X ∩ X = X := by
  apply double_inclusion.mpr
  apply And.intro
  · intro a h₁
    apply And.intro <;> apply h₁
  · intro a h₁
    apply h₁.1

theorem diff_id_left : X // ∅ = X := by
  apply double_inclusion.mpr
  apply And.intro <;> intro a h
  · exact ⟨h, empty_nin a⟩
  · exact h.1

theorem inv_diff_self : X // X = ∅ := by
  apply double_inclusion.mpr
  apply And.intro <;> intro a h
  · contradiction
  · have h₁ : a ∈ X := by exact h.1
    have h₂ : a ∉ X := by exact h.2
    contradiction

theorem inter_empty : X ∩ ∅ = ∅ := by
apply double_inclusion.mpr
apply And.intro <;> intro a h
· contradiction
· exact h.2

theorem union_assoc : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z := by
  apply double_inclusion.mpr
  apply And.intro
  <;> intro a h
  <;> apply Or.elim h
  <;> intro h₁
  · apply Or.elim h₁
    <;> intro h₂
    · apply Or.inl h₂
    · apply Or.inr (Or.inl h₂)
  · apply Or.inr (Or.inr h₁)
  · apply Or.inl (Or.inl h₁)
  · apply Or.elim h₁ <;> intro h₂
    · apply Or.inl (Or.inr h₂)
    · apply Or.inr h₂

theorem union_comm : X ∪ Y = Y ∪ X := by
  apply double_inclusion.mpr
  apply And.intro
  <;> intro a h
  <;> apply Or.elim h
  <;> intro h₁
  · apply Or.inr h₁
  · apply Or.inl h₁
  · apply Or.inr h₁
  · apply Or.inl h₁

theorem inter_comm : X ∩ Y = Y ∩ X := by
  apply double_inclusion.mpr
  apply And.intro
  <;> intro a h
  <;> exact ⟨h.2, h.1⟩

theorem union_inter_dist : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  apply double_inclusion.mpr
  apply And.intro <;> intro a h
  · apply Or.elim h.1 <;> apply Or.elim h.2
    · exact fun h₁ h₂ => Or.inl h₁
    · exact fun h₁ h₂ => Or.inl h₂
    · exact fun h₁ h₂ => Or.inl h₁
    · exact fun h₁ h₂ => Or.inr ⟨h₂, h₁⟩
  · apply Or.elim h
    · exact fun h₁ => ⟨Or.inl h₁, Or.inl h₁⟩
    · exact fun h₁ => ⟨Or.inr h₁.1, Or.inr h₁.2⟩

theorem inter_union_dist : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  apply double_inclusion.mpr
  apply And.intro <;> intro a h
  · apply Or.elim h <;> intro h₁
    · exact ⟨h₁.1, Or.inl h₁.2⟩
    · exact ⟨h₁.1, Or.inr h₁.2⟩
  · apply Or.elim h.2 <;> intro h₁
    · apply Or.inl ⟨h.1, h₁⟩
    · apply Or.inr ⟨h.1, h₁⟩

theorem nin_set_nin_inter : (a ∉ X → a ∉ X ∩ Y) ∧ (a ∉ Y → a ∉ X ∩ Y):= by
  apply And.intro
  <;> intro h
  <;> unfold Nem Not at *
  <;> intro h₁
  · exact h h₁.1
  · exact h h₁.2

theorem diff_union_diff_eq_union_diff_inter : (X // Y) ∪ (Y // X) = (X ∪ Y) // (X ∩ Y) := by
  apply double_inclusion.mpr
  apply And.intro <;> intro a h
  · apply Or.elim h.1 <;> intro h₁
    · exact Or.inl ⟨h₁, fun hy => h.2 ⟨h₁, hy⟩⟩
    · exact Or.inr ⟨h₁, fun hx => h.2 ⟨hx, h₁⟩⟩
  · apply Or.elim h <;> intro h₁
    · exact ⟨Or.inl h₁.1, fun hy => h₁.2 hy.2⟩
    · exact ⟨Or.inr h₁.1, fun hy => h₁.2 hy.1⟩

theorem fam_habit_inter_subs_uni (𝒜 ℬ: Set (Set α)) : (𝒜 ∩ ℬ) habitado → ⋂𝒜 ⊆ ⋃ℬ := by
  intro h x h₁
  unfold Inhabited at h
  obtain ⟨A, h₂⟩ := h
  have hxA : x ∈ A := h₁ A h₂.1
  have h₃: ∃ B, B ∈ ℬ ∧ x ∈ B := ⟨A, h₂.2, hxA⟩
  exact h₃

end CFR
