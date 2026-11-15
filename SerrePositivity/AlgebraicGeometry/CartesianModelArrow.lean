module

public import SerrePositivity.AlgebraicGeometry.FiniteCompositeStageMaps

/-!
概要：同じ係数基底上の具体的な模型と元の射の入力をまとめ、有限族を同じ段へ降ろす。
方針：実際の Cartesian 比較と可換式を保持したまま、既存の有限個の射の降下へ渡す。
規約：模型の存在を主定理の仮定へ追加する出口ではなく、既に供給した入力の整理。
使われ方：G2 の対角の逆・反転・三重交叉の三種の射の同時降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 同じ係数基底上の具体的な源模型と固定標的への元の射の入力。 -/
structure CartesianModelArrow {T S : Scheme.{u}} (g : T ⟶ S) where
  sourceModel : Scheme.{u}
  source : Scheme.{u}
  targetModel : Scheme.{u}
  sourceMap : sourceModel ⟶ S
  targetMap : targetModel ⟶ S
  comparison : source ⟶ sourceModel
  base : source ⟶ T
  cartesian : IsPullback comparison base sourceMap g
  arrow : source ⟶ targetModel
  toBase : arrow ≫ targetMap = base ≫ g
  sourceQC : QuasiCompact sourceMap
  sourceQS : QuasiSeparated sourceMap
  targetFP : LocallyOfFinitePresentation targetMap

/-- 同じ係数基底上の有限族の具体的な射を、一つの共通段の実際の両模型の間の射へ降ろす。 -/
theorem CartesianModelArrow.exists_common_stage
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    [∀ {b d} (q : b ⟶ d), IsAffineHom (D.map q)]
    [∀ b, CompactSpace (D.obj b)] [∀ b, QuasiSeparatedSpace (D.obj b)]
    {S : Scheme.{u}} (γ : D.obj i ⟶ S) (g : c.pt ⟶ S) (hγ : c.π.app i ≫ γ = g)
    {ι : Type v} [Finite ι] (A : ι → CartesianModelArrow g) :
    ∃ (j : Over i)
      (f : ∀ a, pullback (D.map j.hom ≫ γ) (A a).sourceMap ⟶
        pullback (D.map j.hom ≫ γ) (A a).targetMap),
      ∀ a, f a ≫ pullback.fst (D.map j.hom ≫ γ) (A a).targetMap =
          pullback.fst (D.map j.hom ≫ γ) (A a).sourceMap ∧
        (cartesianCompositeStageCone D c i γ (A a).sourceMap g hγ
          (A a).comparison (A a).base (A a).cartesian).π.app j ≫
            f a ≫ pullback.snd (D.map j.hom ≫ γ) (A a).targetMap = (A a).arrow := by
  letI (a : ι) : QuasiCompact (A a).sourceMap := (A a).sourceQC
  letI (a : ι) : QuasiSeparated (A a).sourceMap := (A a).sourceQS
  letI (a : ι) : LocallyOfFinitePresentation (A a).targetMap := (A a).targetFP
  exact exists_finite_compositeStage_maps_of_isLimit D c hc i γ g hγ
    (fun a ↦ (A a).sourceModel) (fun a ↦ (A a).source) (fun a ↦ (A a).targetModel)
    (fun a ↦ (A a).sourceMap) (fun a ↦ (A a).targetMap)
    (fun a ↦ (A a).comparison) (fun a ↦ (A a).base) (fun a ↦ (A a).cartesian)
    (fun a ↦ (A a).arrow) (fun a ↦ (A a).toBase)

end SerrePositivity.AlgebraicGeometry
