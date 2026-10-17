module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraded
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathFlatness

/-! # 固定長 path の両端分解と片側 K-flat 係数 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex

/-- 長さを指定した word。元の word と長さの証拠をそのまま保持する。 -/
abbrev LengthWord {D : Type v} (S : Set D) (n : ℕ) := {w : Word S // w.length = n}

def consLengthWordEquiv {D : Type v} (S : Set D) (n : ℕ) :
    S × LengthWord S n ≃ LengthWord S (n + 1) :=
  Equiv.ofBijective (fun p => ⟨p.1 :: p.2.val, by simp only [List.length_cons, p.2.property]⟩)
    (by
      constructor
      · rintro ⟨b, w⟩ ⟨c, z⟩ h
        have h' := List.cons.inj (congrArg Subtype.val h)
        exact Prod.ext h'.1 (Subtype.ext h'.2)
      · rintro ⟨w, hw⟩
        cases w with
        | nil => simp only [List.length_nil] at hw; omega
        | cons b w =>
          exact ⟨(b, ⟨w, by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hw⟩),
            Subtype.ext rfl⟩)

def reverseLengthWordEquiv {D : Type v} (S : Set D) (n : ℕ) : LengthWord S n ≃ LengthWord S n where
  toFun w := ⟨w.val.reverse, by simpa only [List.length_reverse] using w.property⟩
  invFun w := ⟨w.val.reverse, by simpa only [List.length_reverse] using w.property⟩
  left_inv w := Subtype.ext (List.reverse_reverse w.val)
  right_inv w := Subtype.ext (List.reverse_reverse w.val)

/-- 最後の指定対象と、それ以前の word を取り出す添字同値。 -/
def snocLengthWordEquiv {D : Type v} (S : Set D) (n : ℕ) :
    S × LengthWord S n ≃ LengthWord S (n + 1) :=
  ((Equiv.prodCongr (Equiv.refl S) (reverseLengthWordEquiv S n)).trans
    (consLengthWordEquiv S n)).trans (reverseLengthWordEquiv S (n + 1))

lemma snocLengthWordEquiv_val {D : Type v} (S : Set D) (n : ℕ) (b : S) (w : LengthWord S n) :
    (snocLengthWordEquiv S n (b, w)).val = w.val ++ [b] := by
  change (b :: w.val.reverse).reverse = w.val ++ [b]
  rw [List.reverse_cons, List.reverse_reverse]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Hom(x,b) を先頭に残し、残りを後方係数とする固定長直和の同型。 -/
def fixedLengthSuffixIso (S : Set D) (x y : D) (n : ℕ) :
    fixedLengthHom A D S x y (n + 1) ≅
      ∐ (fun p : S × LengthWord S n => homObject A D x p.1.val ⊗
        pathSuffixWeight A D p.2.val p.1 y) :=
  (Sigma.whiskerEquiv (consLengthWordEquiv S n) (fun _ => Iso.refl _)).symm

/-- Hom(b,y) を末尾に残し、残りを前方係数とする固定長直和の同型。 -/
def fixedLengthPrefixIso (S : Set D) (x y : D) (n : ℕ) :
    fixedLengthHom A D S x y (n + 1) ≅
      ∐ (fun p : S × LengthWord S n => pathPrefixWeight A D p.2.val x p.1 ⊗
        homObject A D p.1.val y) :=
  (Sigma.whiskerEquiv (snocLengthWordEquiv S n) (fun p => by
    change term A D (snocLengthWordEquiv S n p).val x y ≅ _
    rw [snocLengthWordEquiv_val]
    exact termSnocWeightIso A D p.2.val x p.1 y)).symm

/-- 随伴次数部分の前方係数による実際の tensor 直和表示。 -/
def lengthGradedPrefixIso (S : Set D) (x y : D) (n : ℕ) :
    cokernel (lengthMap A D S x y (Nat.le_succ n)) ≅
      ∐ (fun p : S × LengthWord S n => pathPrefixWeight A D p.2.val x p.1 ⊗
        homObject A D p.1.val y) :=
  lengthGradedIso A D S x y n ≪≫ fixedLengthPrefixIso A D S x y n

/-- 随伴次数部分の後方係数による実際の tensor 直和表示。 -/
def lengthGradedSuffixIso (S : Set D) (x y : D) (n : ℕ) :
    cokernel (lengthMap A D S x y (Nat.le_succ n)) ≅
      ∐ (fun p : S × LengthWord S n => homObject A D x p.1.val ⊗
        pathSuffixWeight A D p.2.val p.1 y) :=
  lengthGradedIso A D S x y n ≪≫ fixedLengthSuffixIso A D S x y n

/-- u-small な添字族の余積は非有界 acyclic 複体を保つ。 -/
lemma pathCoproduct_acyclic {I : Type v} [Small.{u} I] (F : I → Complex A)
    (hF : ∀ i, (F i).Acyclic) : (∐ F).Acyclic := by
  have : HasExactColimitsOfShape (Discrete I) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink I).symm)
  exact complex_colimit_acyclic A (Discrete.functor F) (fun i => hF i.as)

/-- 入る側の K-flat 仮定の下で、S から y への Hom が acyclic なら全ての正の層が acyclic。 -/
lemma fixedLengthHom_acyclic_into (S : Set D) (h : homIntoKFlat A D S) (x y : D)
    (hy : ∀ b : S, (homObject A D b.val y).Acyclic) (n : ℕ) :
    (fixedLengthHom A D S x y (n + 1)).Acyclic := by
  have hc := pathCoproduct_acyclic A
    (fun p : S × LengthWord S n => pathPrefixWeight A D p.2.val x p.1 ⊗ homObject A D p.1.val y)
    (fun p => pathPrefixWeight_kFlat A D h p.2.val x p.1 _ (hy p.1))
  exact cochainAcyclic_of_iso hc (fixedLengthPrefixIso A D S x y n).symm

/-- 出る側の K-flat 仮定の下で、x から S への Hom が acyclic なら全ての正の層が acyclic。 -/
lemma fixedLengthHom_acyclic_outOf (S : Set D) (h : homOutOfKFlat A D S) (x y : D)
    (hx : ∀ b : S, (homObject A D x b.val).Acyclic) (n : ℕ) :
    (fixedLengthHom A D S x y (n + 1)).Acyclic := by
  have hc := pathCoproduct_acyclic A
    (fun p : S × LengthWord S n => homObject A D x p.1.val ⊗ pathSuffixWeight A D p.2.val p.1 y)
    (fun p => cochainAcyclic_of_iso (pathSuffixWeight_kFlat A D h p.2.val p.1 y _ (hx p.1))
      (cochainTensorSymmetry (pathSuffixWeight A D p.2.val p.1 y) (homObject A D x p.1.val)))
  exact cochainAcyclic_of_iso hc (fixedLengthSuffixIso A D S x y n).symm

end SerrePositivity.DifferentialGraded.DGQuotient
