namespace CFR
def inj (f : α → β) : Prop := ∀ a a', f a = f a' → a = a
notation f "injetiva" => inj f


end CFR
