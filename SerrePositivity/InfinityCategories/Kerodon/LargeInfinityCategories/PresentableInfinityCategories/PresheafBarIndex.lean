module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafDensity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationUlift

/-!
概要：前層の元の elements 図式を、全単体の bar 添字へ展開する。
方針：elements の単体圏の初頂点写像と次数射影を保持する。
規約：元の前層と密度図式を固定し、退化単体も含める。
使われ方：次数ごとの表現可能前層の小余積と幾何学的実現。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：宇宙を合わせた単体次数における、元の elements の全単体。
方針：次数の持ち上げを忘れる関手に元の単体集合を合成する。
規約：各次数の要素は元の単体そのもの。
使われ方：同じ次数ファイバーの離散余積の縮約。 -/
def presheafBarSimplexFamily : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ) ⥤ Type u :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F

/-- 概要：元の elements の全単体を、制限の向きで取った小さい bar 添字圏。
方針：宇宙を合わせた次数上の要素圏を取る。
規約：同じ全単体と全単体作用素を保持する。
使われ方：密度図式から単体的余積図式への中間添字。 -/
abbrev PresheafBarIndex := (presheafBarSimplexFamily F).Elements

/-- 概要：bar 添字から単体次数への射影。
方針：全単体の要素圏の射影を使う。
規約：全ての面と退化を元の単体作用素のまま保持する。
使われ方：次数ごとの左 Kan 延長による bar 図式。 -/
def presheafBarDegree : PresheafBarIndex F ⥤ ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ) :=
  Functor.Elements.π (presheafBarSimplexFamily F)

/-- 概要：指定次数の全単体を bar 添字へ入れる。
方針：各単体を同じ次数の要素圏対象へ入れる。
規約：有限性や非退化性を要求しない。
使われ方：各次数の小余積を添字付ける離散圏。 -/
def presheafBarFiberInclusion (n : SimplexCategoryᵒᵖ) :
    Discrete ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F).obj n) ⥤ PresheafBarIndex F :=
  Discrete.functor (fun s ↦ (presheafBarSimplexFamily F).elementsMk
    (ULiftHom.objUp (ULift.up n)) s)

omit [Quasicategory C] in
/-- 概要：次数ファイバーの包含は元の次数へ射影される。
方針：要素圏の対象射影を計算する。
規約：単体の値を変更しない。
使われ方：同じ次数の comma における小余積の比較。 -/
lemma presheafBarFiberInclusion_degree (n : SimplexCategoryᵒᵖ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F).obj n) :
    (presheafBarDegree F).obj ((presheafBarFiberInclusion F n).obj (Discrete.mk s)) =
      ULiftHom.objUp (ULift.up n) := rfl

/-- 概要：bar の全単体を元の transport 単体圏へ戻す。
方針：次数の宇宙持ち上げを忘れ、同じ要素と作用素を使う。
規約：退化と全ての面を保持する。
使われ方：元の elements の初頂点写像への接続。 -/
def presheafBarToTransport : PresheafBarIndex F ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F) where
  obj s := ULiftHom.objUp ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F).elementsMk s.obj.objDown.down s.val)
  map f := ⟨{ hom := f.hom.down, map_val := f.map_val }⟩

/-- 概要：元の密度図式を、elements の初頂点写像で全単体へ展開する。
方針：宇宙持ち上げ後の初頂点写像を元の Yoneda 図式へ合成する。
規約：元の密度図式の全高次の作用を保持する。
使われ方：bar 図式の次数ごとの左 Kan 延長への入力。 -/
def presheafBarInputDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (PresheafBarIndex F)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (presheafBarToTransport F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafElementsYonedaDiagram F

/-- 概要：bar 入力の各頂点は同じ初頂点に対応する表現可能前層である。
方針：元の密度図式の頂点公式をそのまま適用する。
規約：同値類ではなく元の関手頂点の等式を与える。
使われ方：各 bar 次数が表現可能前層の小余積であることの判定。 -/
lemma presheafBarInputDiagram_vertex (i : PresheafBarIndex F) :
    (presheafBarInputDiagram F).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F)).app
            (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((presheafBarToTransport F).obj i))))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafElementsYonedaDiagram_vertex F _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
