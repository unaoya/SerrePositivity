module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeEndNullHomotopy
public import SerrePositivity.KST.SConstruction.DGStrictNatTransHomEnd
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle

/-!
概要：元厳密比較・元 cone 包含・元零化を全 dg 関手圏の実二単体へ束ねる。
方針：同じ end 内で微分を元全合成へ同定し、dg nerve の実二単体構成子を使う。
規約：指定三辺と元左包含の次数 −1 成分を保持する。
使われ方：元 cone 全族を cofiber 図式と逆回転へ運ぶための指定零化面。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => dgModuleNaturalConeFunctor R D F G η
local notation "i" => dgModuleNaturalConeInr R D F G η
local notation "h" => dgModuleNaturalConeEndNullHomotopy R D F G η

/-- 概要：同じ end 零化元の微分は元全厳密合成の end 元。
方針：全評価で元二閉射の合成と同じ左包含境界を照合する。
規約：元厳密合成を保持。使われ方：元指定零化面の境界。 -/
lemma dgModuleNaturalConeEndNullHomotopy_d :
    (dgFunctorHom R P (RightModule R D) F (T)).d (-1) 0 (h) =
      dgStrictNatTransEndElement R P (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η (i)) := by
  apply dgFunctorHomElement_ext R P (RightModule R D)
  intro x
  rw [dgModuleNaturalConeEndNullHomotopy_d_π, dgStrictNatTransEndElement_π]
  have hc := dgModuleNaturalConeArrow_cycle R D F (T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η (i)) x
  rw [dgModuleNaturalConeArrow_comp, dgModuleNaturalConeInr_arrow] at hc
  exact hc

/-- 概要：元比較と cone 包含の end 内合成は元厳密合成の同じ end 元。
方針：全評価の豊穣合成保存と元閉零成分を使う。
規約：元二辺を保持。使われ方：実二単体の合成辺の認証。 -/
lemma dgModuleNaturalConeEndBoundary_comp :
    compose R (x := F) (y := G) (z := (T)) (dgStrictNatTransEndElement R P (RightModule R D) (i))
      (dgStrictNatTransEndElement R P (RightModule R D) η) (zero_add 0) =
    dgStrictNatTransEndElement R P (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η (i)) := by
  apply dgFunctorHomElement_ext R P (RightModule R D)
  intro x
  change (dgFunctorHomπ R P (RightModule R D) F (T) x).f 0
      (((0 : ℤ) * 0).negOnePow • forward R (x := F) (y := G) (z := (T))
        (dgStrictNatTransEndElement R P (RightModule R D) η)
        (dgStrictNatTransEndElement R P (RightModule R D) (i)) (zero_add 0)) = _
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  have hc := DGFunctor.map_forward R (dgFunctorEvaluationDG R P (RightModule R D) x)
    (x := F) (y := G) (z := (T))
    (dgStrictNatTransEndElement R P (RightModule R D) η)
    (dgStrictNatTransEndElement R P (RightModule R D) (i)) (zero_add 0)
  change (dgFunctorHomπ R P (RightModule R D) F (T) x).f 0
      (forward R (x := F) (y := G) (z := (T))
        (dgStrictNatTransEndElement R P (RightModule R D) η)
        (dgStrictNatTransEndElement R P (RightModule R D) (i)) (zero_add 0)) =
    forward R ((dgFunctorHomπ R P (RightModule R D) F G x).f 0
      (dgStrictNatTransEndElement R P (RightModule R D) η))
      ((dgFunctorHomπ R P (RightModule R D) G (T) x).f 0
        (dgStrictNatTransEndElement R P (RightModule R D) (i))) (zero_add 0) at hc
  rw [hc]
  rw [dgStrictNatTransEndElement_π, dgStrictNatTransEndElement_π,
    dgStrictNatTransEndElement_π]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp, compose, zero_mul, Int.negOnePow_zero, one_smul]

/-- 概要：元比較・元 cone 包含・零辺と同じ end 零化を持つ三角形データ。
方針：元全合成と微分の二つの end 等号を使用する。
規約：対象族と指定原始元を変更しない。使われ方：全関手圏の実二単体。 -/
def dgModuleNaturalConeEndTriangleData : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData R (DGFunctor R P (RightModule R D)) where
  obj := ![F, G, (T)]
  f01 := dgStrictNatTransEndCycle R P (RightModule R D) η
  f12 := dgStrictNatTransEndCycle R P (RightModule R D) (i)
  f02 := ⟨0, by change (homObject R (DGFunctor R P (RightModule R D)) F (T)).d 0 1 0 = 0
                exact map_zero _⟩
  homotopy := (h)
  differential_homotopy := by
    change (dgFunctorHom R P (RightModule R D) F (T)).d (-1) 0 (h) =
      compose R (x := F) (y := G) (z := (T))
        (dgStrictNatTransEndElement R P (RightModule R D) (i))
        (dgStrictNatTransEndElement R P (RightModule R D) η) (zero_add 0) - 0
    rw [sub_zero]
    exact (dgModuleNaturalConeEndNullHomotopy_d R D F G η).trans
      (dgModuleNaturalConeEndBoundary_comp R D F G η).symm

/-- 概要：元 cone の指定零化面を全 dg 関手圏の native nerve の実二単体にする。
方針：同じ end 三角形データをそのまま実単体へ写す。
規約：元全 Hom と次数 −1 成分を保持。使われ方：全 cone 図式の組立て。 -/
def dgModuleNaturalConeEndTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R P (RightModule R D)) 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndTriangleData R D F G η)

end SerrePositivity.KST.SConstruction
