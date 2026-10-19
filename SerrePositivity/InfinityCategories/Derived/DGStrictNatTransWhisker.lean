module
public import SerrePositivity.InfinityCategories.DGNerve.NatTrans
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaStrict

/-! # 厳密 dg 自然変換の dg 関手による前後合成

概要：厳密自然変換を dg 関手で前後から写し、全斉次自然性を保つ。
方針：前合成は成分を評価し、後合成は閉零元を写して合成保存を使う。
規約：通常の閉零圏の自然性へ弱めない。使われ方：実屋根 prism の商自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {B C D E : Type v}
variable [DGCategory A B] [DGCategory A C] [DGCategory A D] [DGCategory A E]
variable {F G : DGFunctor A C D}

/-- 厳密 dg 自然変換の閉零成分と全斉次自然性を dg 関手で写す。 -/
def dgStrictNatTransPostcomp (η : StrictNatTrans F G) (Q : DGFunctor A D E) :
    StrictNatTrans (F.comp Q) (G.comp Q) where
  app x := ⟨(Q.map (F.obj x) (G.obj x)).f 0 (η.app x).val, by
    exact (map_differential Q (η.app x).val).symm.trans
      ((congrArg ((Q.map (F.obj x) (G.obj x)).f 1) (η.app x).property).trans
        ((Q.map (F.obj x) (G.obj x)).f 1).hom.map_zero)⟩
  naturality {x y} {k} f := by
    change compose A ((Q.map _ _).f 0 (η.app y).val)
      ((Q.map _ _).f k ((F.map x y).f k f)) (add_zero k) =
      compose A ((Q.map _ _).f k ((G.map x y).f k f))
        ((Q.map _ _).f 0 (η.app x).val) (zero_add k)
    exact (map_compose Q (η.app y).val ((F.map x y).f k f) (add_zero k)).symm.trans
      ((congrArg ((Q.map (F.obj x) (G.obj y)).f k) (η.naturality f)).trans
        (map_compose Q ((G.map x y).f k f) (η.app x).val (zero_add k)))

/-- 相の対象を後合成で写すことと、後合成後の相を選ぶことは一致する。 -/
lemma dgStrictNatTransPostcomp_phase (Q : DGFunctor A D E) (i : Fin 2) (x : C) :
    StrictNatTrans.phaseObj (F.comp Q) (G.comp Q) i x =
      Q.obj (StrictNatTrans.phaseObj F G i x) := by
  fin_cases i <;> rfl

/-- 二相間の斉次写像は後合成の元の dg Hom 写像と一致する。 -/
lemma dgStrictNatTransPostcomp_transition (η : StrictNatTrans F G) (Q : DGFunctor A D E)
    {x y : C} {k : ℤ} (i j : Fin 2) (h : i ≤ j) (f : GradedHom A x y k) :
    HEq ((dgStrictNatTransPostcomp η Q).transition i j h f)
      ((Q.map (StrictNatTrans.phaseObj F G i x) (StrictNatTrans.phaseObj F G j y)).f k
        (η.transition i j h f)) := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact heq_of_eq (map_compose Q (η.app y).val ((F.map x y).f k f) (add_zero k)).symm
  · exact False.elim ((by decide : ¬ ((1 : Fin 2) ≤ 0)) h)
  · rfl

/-- 二相間の斉次写像は、前合成の元の dg Hom 写像を適用した写像と一致する。 -/
lemma dgStrictNatTransPrecomp_transition (P : DGFunctor A B C) (η : StrictNatTrans F G)
    {x y : B} {k : ℤ} (i j : Fin 2) (h : i ≤ j) (f : GradedHom A x y k) :
    (dgStrictNatTransPrecomp P η).transition i j h f =
      η.transition i j h ((P.map x y).f k f) := by
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((1 : Fin 2) ≤ 0)) h)
  · rfl

end SerrePositivity.InfinityCategories
