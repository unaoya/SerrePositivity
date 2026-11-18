module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeAWProjectedEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.StandardDoldKanZeroRawEvaluation

/-!
# 指定自由正規化 Hom の零次数評価

概要：自由生成元の零次数像を元の閉元の包含で評価する。
方針：零次数のMoore包含の同型と指定DK零次数公式を使う。
規約：smart切断のcyclesを保ち、正次数の式と合わせて全次数を扱う。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）のG10の全単体の指定合成の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology DifferentialGraded MonoidalCategory
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R]

/-- 概要：零次数の指定Moore射影は元の包含同型の逆射。
方針：同じ包含の後で射影の因子分解を使う。
規約：単体的加群は任意。使われ方：HA 1.2.4 の指定生成元の零次数評価。 -/
theorem mooreProjection_zero_eq (W : SimplicialObject (ModuleCat R)) :
    (DoldKan.PInftyToNormalizedMooreComplex W).f 0 = (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv := by
  apply (cancel_mono (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).hom).mp
  rw [Iso.inv_hom_id]
  change (DoldKan.PInftyToNormalizedMooreComplex W).f 0 ≫
    (inclusionOfMooreComplexMap W).f 0 = 𝟙 _
  rw [← HomologicalComplex.comp_f,
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
    DoldKan.PInfty_f_0]

/-- 概要：同じ自由逆随伴の零次数像は元のΓ零次数評価。
方針：一般の射影生成元評価に零次数射影の式を代入する。
規約：同じ自由随伴。使われ方：HA 1.2.4 の閉元の包含への接続。 -/
theorem normalizedFreeHomEquiv_symm_zero_eval (S : SSet.{u})
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : S ⟶ (Abelian.DoldKan.Γ.obj K) ⋙ forget (ModuleCat R))
    (s : S.obj (Opposite.op ⦋0⦌)) :
    (((freeMooreChainsAdjunction (R := R)).homEquiv S K).symm f).f 0
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (S ⋙ ModuleCat.free R)).inv (ModuleCat.freeMk s)) =
    (_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso K).hom (f.app _ s) := by
  have h := normalizedFreeHomEquiv_symm_projected_eval S K f 0 s
  rw [mooreProjection_zero_eq, mooreProjection_zero_eq] at h
  exact h

variable {D : Type v} [DGCategory R D]

/-- 概要：実標準Homの逆随伴の零次数像は元の最上位成分。
方針：同じ自由随伴の零次数公式と既存の生のDK評価を合成する。
規約：cyclesからの包含を明記する。使われ方：HA 1.2.4 の実合成の零次数照合。 -/
theorem normalizedFreeStandardHom_zero_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (s : S.obj (Opposite.op ⦋0⦌)) :
    (homObject R D x y).iCycles 0
      ((connectiveHomComplex_zeroIso (R := R) x y).hom
        ((normalizedFreeStandardHom S x y f).f 0
          ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso (S ⋙ ModuleCat.free R)).inv (ModuleCat.freeMk s)))) =
    standardTopEval (R := R) x y 0 (f.app _ s) := by
  let t : S ⟶ (Abelian.DoldKan.Γ.obj (connectiveHomComplex (R := R) x y)) ⋙
      forget (ModuleCat R) := f ≫ standardDoldKanSpaceMap x y
  have h := normalizedFreeHomEquiv_symm_zero_eval S
    (connectiveHomComplex (R := R) x y) t s
  have hp := congrArg (fun a => (homObject R D x y).iCycles 0
    ((connectiveHomComplex_zeroIso (R := R) x y).hom a)) h
  have he := _root_.SerrePositivity.ComplexLimits.standardDoldKanModuleIso_zero_raw (R := R) x y (f.app _ s)
  rw [_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion_cycles] at he
  change (homObject R D x y).iCycles 0
    ((connectiveHomComplex_zeroIso (R := R) x y).hom
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (connectiveHomComplex (R := R) x y)).hom
        ((standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋0⦌)
          (f.app _ s)))) = _ at he
  dsimp only [t, standardDoldKanSpaceMap, NatTrans.comp_app, Functor.whiskerRight_app] at hp
  exact hp.trans he

/-- 概要：実AW合成の自由逆随伴を零次数でも同じ切断和で評価する。
方針：閉元への包含つき生成元評価を実標準合成に適用する。
規約：後の射gを第一因子とする。使われ方：HA 1.2.4 の全次数の指定合成照合。 -/
theorem normalizedFreeStandardAW_zero_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y)
    (s : S.obj (Opposite.op ⦋0⦌)) (t : T.obj (Opposite.op ⦋0⦌)) :
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
    (homObject R D x z).iCycles 0
      ((connectiveHomComplex_zeroIso (R := R) x z).hom
        ((normalizedFreeStandardHom (S ⊗ T) x z h).f 0
          ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((S ⊗ T) ⋙ ModuleCat.free R)).inv
            (ModuleCat.freeMk (s, t)))) ) =
    ∑ j : (Finset.univ : Finset (Fin 1)),
      awTerm (g.app _ s).val (f.app _ t).val Finset.univ j 0 (by simp) := by
  let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
  have he := normalizedFreeStandardHom_zero_eval (S ⊗ T) x z h (s, t)
  exact he.trans (by rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
