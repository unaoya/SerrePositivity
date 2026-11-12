module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeEndTriangle
public import SerrePositivity.KST.SConstruction.DGClosedZeroHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeSquare

/-!
概要：元 cone の全 end 零化面に同じ零角を貼り、全 dg 関手圏内の実四角形を構成する。
方針：元下二単体を変更せず、指定零対角を共有する零上二単体を貼る。
規約：元次数 −1 元・元比較・元包含・実零加群を保持する。
使われ方：元 cone 全族の押し出し性と逆回転全図式比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories

open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：同じ全 cone 図式に使う実零加群の定数 dg 関手。
方針：元閉零対象をそのまま使う。規約：同じ対象値を保持。
使われ方：全 end 四角形の指定零角。 -/
def dgModuleNaturalConeEndZero : DGFunctor R P (RightModule R D) :=
  dgClosedZeroFunctor R (ForgetEnrichment.to (Complex R) (moduleZero R D))
    (moduleZero_isZero R D) P
local notation "Z" => dgModuleNaturalConeEndZero R D (P := P)

/-- 概要：元零対角を共有し同じ実零関手を経由する上三角形データ。
方針：元三零辺と零原始元を指定する。
規約：零角を選び直さない。使われ方：元下零化面との貼合せ。 -/
def dgModuleNaturalConeEndZeroTriangleData :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData R (DGFunctor R P (RightModule R D)) where
  obj := ![F, (Z), (T)]
  f01 := ⟨0, by change (homObject R _ F (Z)).d 0 1 0 = 0; exact map_zero _⟩
  f12 := ⟨0, by change (homObject R _ (Z) (T)).d 0 1 0 = 0; exact map_zero _⟩
  f02 := ⟨0, by change (homObject R _ F (T)).d 0 1 0 = 0; exact map_zero _⟩
  homotopy := 0
  differential_homotopy := by
    change (homObject R (DGFunctor R P (RightModule R D)) F (T)).d (-1) 0 0 = compose R
      (x := F) (y := (Z)) (z := (T)) (0 : GradedHom R (Z) (T) 0)
      (0 : GradedHom R F (Z) 0) (zero_add 0) - (0 : GradedHom R F (T) 0)
    rw [map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero]

/-- 概要：同じ元下二単体と実零上二単体を貼った全 end cone 四角形。
方針：指定零対角の厳密一致で正方形の pushout を使う。
規約：元下二単体を保持。使われ方：native 全関手族への全図式評価。 -/
def dgModuleNaturalConeEndSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v w}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndZeroTriangleData R D F G η)))
    (SSet.yonedaEquiv.symm (dgModuleNaturalConeEndTriangle R D F G η)) (by
      let X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D))
      let upper := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndZeroTriangleData R D F G η)
      let lower := dgModuleNaturalConeEndTriangle R D F G η
      have hU := stdSimplex.δ_comp_yonedaEquiv_symm (X := X) (n := 1) upper (1 : Fin 3)
      have hL := stdSimplex.δ_comp_yonedaEquiv_symm (X := X) (n := 1) lower (1 : Fin 3)
      have hd : X.δ 1 upper = X.δ 1 lower :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.triangle_face02 (dgModuleNaturalConeEndZeroTriangleData R D F G η)).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.triangle_face02 (dgModuleNaturalConeEndTriangleData R D F G η)).symm
      exact hU.trans ((congrArg (fun s : X _⦋1⦌ => SSet.yonedaEquiv.symm s) hd).trans hL.symm))

/-- 概要：全 end 四角形の下二単体は元の指定零化面そのもの。
方針：貼合せの右包含則を使う。規約：次数 −1 の元全族を保持。
使われ方：元実逆回転との全図式比較。 -/
lemma dgModuleNaturalConeEndSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgModuleNaturalConeEndSquare R D F G η =
      SSet.yonedaEquiv.symm (dgModuleNaturalConeEndTriangle R D F G η) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 概要：全 end 四角形の上二単体は同じ実零角を経る指定面。
方針：貼合せの左包含則を使う。規約：同じ零対角を保持。
使われ方：全 cone 四角形の点評価。 -/
lemma dgModuleNaturalConeEndSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgModuleNaturalConeEndSquare R D F G η =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndZeroTriangleData R D F G η)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

end SerrePositivity.KST.SConstruction
