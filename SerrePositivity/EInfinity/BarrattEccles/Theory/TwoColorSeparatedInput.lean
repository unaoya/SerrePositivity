module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorStandardAction

/-!
# 二色の標準入力と分離された冪の表現の複体

HA 3.2.4.7 の自由比較のため、指定標準入力の同型を
実際の二色部分群上の表現の複体の同型へ持ち上げる。
各次数の作用だけでなく、元の複体の微分と指定した順射を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

section RepresentationIso
variable {A G : Type u} [CommRing A] [Group G] {K L : Complex A}

/-- 同変な複体の同型は、同じ順射を持つ表現の複体の同型へ持ち上がる。 -/
def representationCochainIso (ρ : G →* End K) (σ : G →* End L) (e : K ≅ L)
    (he : ∀ g, (ρ g).asHom ≫ e.hom = e.hom ≫ (σ g).asHom) :
    representationCochainComplex ρ ≅ representationCochainComplex σ where
  hom := representationCochainMap ρ σ e.hom he
  inv := representationCochainMap σ ρ e.inv (by
    intro g
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← he g, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply (forget₂ (Rep.{u} A G) (ModuleCat A)).map_injective
    exact congrArg (fun f => f.f i) e.hom_inv_id
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply (forget₂ (Rep.{u} A G) (ModuleCat A)).map_injective
    exact congrArg (fun f => f.f i) e.inv_hom_id

/-- 持ち上げた同型の順射も、指定された元の複体の射である。 -/
lemma representationCochainIso_hom (ρ : G →* End K) (σ : G →* End L) (e : K ≅ L)
    (he : ∀ g, (ρ g).asHom ≫ e.hom = e.hom ≫ (σ g).asHom) :
    (representationCochainIso ρ σ e he).hom = representationCochainMap ρ σ e.hom he := rfl

end RepresentationIso
namespace BarrattEccles
variable {A : Type u} [CommRing A] (X Y : Complex A) (m n : ℕ)

/-- 二色部分群の、左入力のテンソル冪への実際の置換作用。 -/
def twoColorLeftInputAction : TwoColorGroup.{u} m n →* End (power X m) :=
  Aut.toEnd.comp ((permutationAction X m).comp
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin m)) ≃* Equiv.Perm (Fin m)).toMonoidHom.comp
      (twoColorLeftProjection m n)))

/-- 二色部分群の、右入力のテンソル冪への実際の置換作用。 -/
def twoColorRightInputAction : TwoColorGroup.{u} m n →* End (power Y n) :=
  Aut.toEnd.comp ((permutationAction Y n).comp
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin n)) ≃* Equiv.Perm (Fin n)).toMonoidHom.comp
      (twoColorRightProjection m n)))

/-- 分離した左右の冪を、対角作用と元の微分を持つ表現の複体として読む。 -/
def twoColorSeparatedInput : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ :=
  representationCochainComplex
    (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))

/-- 指定された標準入力の分離は、表現の複体そのものの同型である。 -/
def twoColorStandardSeparatedIso :
    twoColorStandardInput X Y m n ≅ twoColorSeparatedInput X Y m n :=
  representationCochainIso
    (binaryTensorWordFixedAction X Y (m + n) (binaryTensorStandardPattern m n)
      (twoColorInputPermutation m n) (twoColorInputPermutation_fixed m n))
    (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
    (binaryTensorStandardPowersIso X Y m n) (twoColorStandardPowersIso_action X Y m n)

/-- 分離同型の忘却した各次数は、指定された標準パターンの分離射そのもの。 -/
lemma twoColorStandardSeparatedIso_hom_f (i : ℤ) :
    (forget₂ (Rep.{u} A (TwoColorGroup.{u} m n)) (ModuleCat A)).map
      ((twoColorStandardSeparatedIso X Y m n).hom.f i) =
        (binaryTensorStandardPowersIso X Y m n).hom.f i := rfl

end BarrattEccles
end SerrePositivity.EInfinity
