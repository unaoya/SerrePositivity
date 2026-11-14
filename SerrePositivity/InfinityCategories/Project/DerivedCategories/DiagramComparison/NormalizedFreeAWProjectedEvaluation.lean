module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomProjectedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardComposition

/-!
# 実標準 AW 合成の自由正規化鎖への逆随伴

概要：実豊穣合成の自由鎖逆随伴を同じ切断点の和で計算する。
方針：指定逆随伴の生成元評価を実標準合成に適用する。
規約：反転前の重みを第一因子、Homパラメータを第二因子に置く。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）のG10の指定比較射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology DifferentialGraded MonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：実標準Homへの射を指定自由鎖随伴で戻す。
方針：同じDK忘却射の逆随伴。規約：選び直した射ではない。
使われ方：HA 1.2.4 のAW比較の実成分表示。 -/
def normalizedFreeStandardHom (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) :
    (normalizedMooreComplex (ModuleCat R)).obj (S ⋙ ModuleCat.free R) ⟶
      connectiveHomComplex (R := R) x y :=
  ((freeMooreChainsAdjunction (R := R)).homEquiv S
    (connectiveHomComplex (R := R) x y)).symm (f ≫ standardDoldKanSpaceMap x y)

/-- 概要：実AW合成の逆随伴を自由生成元で評価すると同じ全切断和となる。
方針：標準合成の台の定義と正次数生成元評価。
規約：gが後の射、fが前の射。使われ方：HA 1.2.4 の指定AW比較の成分照合。 -/
theorem normalizedFreeStandardAW_positive_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n + 1⦌)) (t : T.obj (Opposite.op ⦋n + 1⦌)) :
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
    (connectiveHomComplex_positiveIso (R := R) x z n).hom
      ((normalizedFreeStandardHom (S ⊗ T) x z h).f (n + 1)
        ((DoldKan.PInftyToNormalizedMooreComplex ((S ⊗ T) ⋙ ModuleCat.free R)).f (n + 1)
          (ModuleCat.freeMk (s, t)))) =
    ∑ j : (Finset.univ : Finset (Fin (n + 2))),
      awTerm (g.app _ s).val (f.app _ t).val Finset.univ j (-(n + 1 : ℤ)) (by simp) := by
  let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
  have he := normalizedFreeStandardHom_positive_eval (S ⊗ T) x z h n (s, t)
  exact he.trans (by rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
