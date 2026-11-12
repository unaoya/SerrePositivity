module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionDiagram

/-!
概要：初頂点写像の底に関する自然性と反転する射への作用。
方針：要素の圏の射と初頂点座標の同じ値を比較する。
規約：始点を保つ射は元の底で実際の退化辺になる。
使われ方：単体圏上の共同切断評価の降下の基底の条件。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底の射は全単体の切断の添字圏の関手を定める。
方針：要素の圏の関手を射の宇宙の持ち上げの間に挟む。
規約：次数と単体作用素をそのまま保持する。
使われ方：初頂点写像の底変換の自然性。 -/
def transportSimplexFunctor {B D : SSet.{u}} (f : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D :=
  ULiftHom.down ⋙ f.mapElements ⋙ ULiftHom.up

/-- 概要：初頂点の作用素は底の射で単体を写しても変わらない。
方針：要素の圏の射の下の単体作用素が不変なことを使う。
規約：関手の対象の単体の値だけが変わる。
使われ方：底の射に関する自然性の座標計算。 -/
lemma transportSimplexFirstVertexMorphism_map {B D : SSet.{u}} (f : B ⟶ D) {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (σ ⋙ transportSimplexFunctor f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism σ := rfl

/-- 概要：初頂点写像は任意の底の射に関して厳密に自然。
方針：初頂点座標の不変性と底の射の単体的自然性を使う。
規約：底は任意の単体集合。
使われ方：共同切断評価の降下を底と同時に比較する。 -/
lemma transportSimplexFirstVertexMap_naturality {B D : SSet.{u}} (f : B ⟶ D) :
    nerveMap (transportSimplexFunctor f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B ≫ f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change D.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism σ).op (f.app _ (σ.obj 0).objDown.val) =
    f.app _ (B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism σ).op (σ.obj 0).objDown.val)
  exact (f.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism σ).op _).symm

/-- 概要：初頂点写像は指定単体の頂点で元の単体の最初の頂点を返す。
方針：長さ零の射列の初頂点座標を計算する。
規約：底上の標準単体の実際の射で値を表示する。
使われ方：共同切断評価の始点評価と元の底の頂点を揃える。 -/
lemma transportSimplexFirstVertexMap_vertex {B : SSet.{u}} {n : SimplexCategory}
    (σ : B.obj (Opposite.op n)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ)) =
      (SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1))) := rfl

/-- 概要：始点を保つ条件は下の単体作用素が零を零へ送ることと同値。
方針：最初の頂点の可換式を零頂点で評価し、逆は全次数で計算する。
規約：作用素は退化を含んでよい。
使われ方：初頂点写像が反転する射を具体的に判定する。 -/
lemma transportSimplexPreservesFirst_iff {B : SSet.{u}}
    {i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexPreservesFirst f ↔ f.down.hom.unop.toOrderHom 0 = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun g : (Δ[0] : SSet.{u}) ⟶ stdSimplex.obj i.objDown.obj.unop ↦
      (SSet.yonedaEquiv g).down.toOrderHom 0) h
    exact hv
  · intro h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex j.objDown.obj.unop.len ≫ stdSimplex.map f.down.hom.unop =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex i.objDown.obj.unop.len
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply stdSimplex.ext
    intro k
    exact h

/-- 概要：始点を保つ添字の射は初頂点写像で実際の退化辺へ写る。
方針：射の二つの初頂点座標を零へ揃え、単体作用素の合成則を使う。
規約：ホモトピー類だけの一致には弱めない。
使われ方：共同切断評価の局所化による降下で反転する射の検証。 -/
lemma transportSimplexFirstVertexMap_edge_of_preservesFirst {B : SSet.{u}}
    {i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : i ⟶ j) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexPreservesFirst f) :
    ((nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)).edge =
      (SSet.Edge.id ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge := by
  have hcoord : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (ComposableArrows.mk₁ f) =
      SimplexCategory.σ (0 : Fin 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (ComposableArrows.mk₀ i) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    fin_cases k
    · rfl
    · exact (transportSimplexPreservesFirst_iff f).mp hf
  change B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (ComposableArrows.mk₁ f)).op i.objDown.val =
    B.map (SimplexCategory.σ (0 : Fin 1)).op
      (B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (ComposableArrows.mk₀ i)).op i.objDown.val)
  rw [hcoord]
  exact (B.map_comp _ _).symm ▸ rfl

/-- 概要：初頂点写像は元の底の全ての頂点を被覆する。
方針：各頂点を零単体として添字圏へ入れ、その初頂点を計算する。
規約：底の充填性や小ささの追加仮定は不要。
使われ方：初頂点写像に沿う降下の対象の被覆。 -/
lemma transportSimplexFirstVertexMap_vertex_surjective (B : SSet.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)) := by
  intro b
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) b), ?_⟩
  rw [transportSimplexFirstVertexMap_vertex]
  have h : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [h, SSet.yonedaEquiv_symm_app_id]

/-- 概要：初頂点写像は対象について本質的全射。
方針：頂点の厳密な被覆からホモトピー圏の恒等的な同型を取る。
規約：この主張だけから局所化の普遍性は結論しない。
使われ方：局所化の比較の対象の被覆の検証。 -/
lemma transportSimplexFirstVertexMap_isEssentiallySurjective (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) := by
  intro b
  obtain ⟨a, ha⟩ := transportSimplexFirstVertexMap_vertex_surjective B b
  exact ⟨a, ⟨eqToIso (congrArg SSet.HomotopyCategory.mk ha)⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
