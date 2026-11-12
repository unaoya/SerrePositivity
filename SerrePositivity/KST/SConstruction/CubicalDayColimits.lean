module
public import SerrePositivity.KST.SConstruction.CubicalExternalColimits
public import SerrePositivity.KST.SConstruction.CubicalDayKanComparison
public import SerrePositivity.KST.SConstruction.CubicalDayRepresentableNaturality

/-! # 元の cubical Day tensor の各変数の余極限保存
概要：元の全 cubical 前層の Day tensor は左右それぞれで余極限を保つ。
方針：外積と左 Kan 延長の合成から、元の生成射に自然な比較同型で移す。
規約：閉構造を仮定しない。使われ方：元の necklace 合成の余極限への降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits

/-- 元の左因子を固定した Day tensor 関手。 -/
def cubicalDayTensorLeft (K : CubicalSet.{u}) : CubicalSet.{u} ⥤ CubicalSet.{u} :=
  ((Functor.const CubicalSet.{u}).obj K).prod' (𝟭 _) ⋙ cubicalDayTensorFunctor

/-- 元の右因子を固定した Day tensor 関手。 -/
def cubicalDayTensorRight (L : CubicalSet.{u}) : CubicalSet.{u} ⥤ CubicalSet.{u} :=
  (𝟭 _).prod' ((Functor.const CubicalSet.{u}).obj L) ⋙ cubicalDayTensorFunctor

/-- 左因子を固定した外積の Kan 延長と元の Day tensor の自然同型。 -/
def cubicalDayKanLeftIso (K : CubicalSet.{u}) :
    cubicalExternalLeft K ⋙ (tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lan ≅ cubicalDayTensorLeft K :=
  NatIso.ofComponents (fun L => cubicalDayKanIso K L)
    (fun f => cubicalDayKanIso_naturality (𝟙 K) f)

/-- 右因子を固定した外積の Kan 延長と元の Day tensor の自然同型。 -/
def cubicalDayKanRightIso (L : CubicalSet.{u}) :
    cubicalExternalRight L ⋙ (tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lan ≅ cubicalDayTensorRight L :=
  NatIso.ofComponents (fun K => cubicalDayKanIso K L)
    (fun f => cubicalDayKanIso_naturality f (𝟙 L))

/-- 具体的立方体の tensor に沿う左 Kan 延長は、同じ大きさの余極限を保つ。 -/
instance cubicalTensorKan_preservesColimits : PreservesColimitsOfSize.{u, u}
    ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lan (H := Type u)) :=
  ((tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ).lanAdjunction (Type u)).leftAdjoint_preservesColimits

/-- 元の左因子を固定した Day tensor は余極限を保つ。 -/
instance cubicalDayTensorLeft_preservesColimits (K : CubicalSet.{u}) :
    PreservesColimitsOfSize.{u, u} (cubicalDayTensorLeft K) :=
  preservesColimits_of_natIso (cubicalDayKanLeftIso K)

/-- 元の右因子を固定した Day tensor は余極限を保つ。 -/
instance cubicalDayTensorRight_preservesColimits (L : CubicalSet.{u}) :
    PreservesColimitsOfSize.{u, u} (cubicalDayTensorRight L) :=
  preservesColimits_of_natIso (cubicalDayKanRightIso L)

end SerrePositivity.KST.SConstruction
