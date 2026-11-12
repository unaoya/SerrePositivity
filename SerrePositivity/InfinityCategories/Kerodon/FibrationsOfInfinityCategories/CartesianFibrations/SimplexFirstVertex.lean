module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexDomains

/-!
概要：単体圏の nerve から元の底への初頂点写像。
方針：制限の射列の各段の初頂点を最初の単体内へ戻し、その単調列で評価する。
規約：面と退化を同じ自然性の式で保つ。
使われ方：全単体の共同切断評価を元の底へ降ろす基底の写像。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：単体の制限の射列から最初の単体内の頂点の単調列を取る。
方針：各段の初頂点を零段からの射で戻し、射列の合成則で単調性を示す。
規約：零段の頂点は零であり、恒等や退化を含む。
使われ方：初頂点写像の各次数の座標。 -/
def transportSimplexFirstVertexOrderHom {B : SSet.{u}} {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) :
    Fin (n + 1) →o Fin ((σ.obj 0).objDown.obj.unop.len + 1) where
  toFun i := (σ.map (homOfLE (Fin.zero_le i))).down.hom.unop.toOrderHom 0
  monotone' i j hij := by
    have hm : σ.map (homOfLE (Fin.zero_le j)) =
        σ.map (homOfLE (Fin.zero_le i)) ≫ σ.map (homOfLE hij) :=
      σ.map_comp (homOfLE (Fin.zero_le i)) (homOfLE hij)
    change (σ.map (homOfLE (Fin.zero_le i))).down.hom.unop.toOrderHom 0 ≤
      (σ.map (homOfLE (Fin.zero_le j))).down.hom.unop.toOrderHom 0
    rw [hm]
    exact (σ.map (homOfLE (Fin.zero_le i))).down.hom.unop.toOrderHom.monotone
      (Fin.zero_le _)

/-- 概要：射列の初頂点の単調列を標準単体の作用素として表す。
方針：単調写像から単体圏の射を作る。
規約：値域は最初の単体の次数。
使われ方：元の底の最初の単体を評価する作用素。 -/
def transportSimplexFirstVertexMorphism {B : SSet.{u}} {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) :
    ⦋n⦌ ⟶ (σ.obj 0).objDown.obj.unop :=
  SimplexCategory.mkHom (transportSimplexFirstVertexOrderHom σ)

/-- 概要：射列を制限した初頂点座標は最初の単体への制限の射と可換。
方針：零段から各段への射を、中間の零段を通る二つの射へ分解する。
規約：作用素は単射に限定しない。
使われ方：初頂点写像の面・退化の自然性。 -/
lemma transportSimplexFirstVertexMorphism_naturality {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n.len) :
    transportSimplexFirstVertexMorphism ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) ≫
        (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))).down.hom.unop =
      α ≫ transportSimplexFirstVertexMorphism σ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  have hm : σ.map (homOfLE (Fin.zero_le (α.toOrderHom i))) =
      σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))) ≫
        σ.map (homOfLE (α.toOrderHom.monotone (Fin.zero_le i))) :=
    (σ.map_comp (homOfLE (Fin.zero_le (α.toOrderHom 0)))
      (homOfLE (α.toOrderHom.monotone (Fin.zero_le i))))
  exact (congrArg (fun f : σ.obj 0 ⟶ σ.obj (α.toOrderHom i) ↦
    f.down.hom.unop.toOrderHom 0) hm).symm

/-- 概要：単体の制限の n 射列を元の底の n 単体に評価する。
方針：最初の単体を初頂点座標の作用素で制限する。
規約：各次数で実際の底の単体を返す。
使われ方：単体圏の nerve からの初頂点写像。 -/
def transportSimplexFirstVertexSimplex {B : SSet.{u}} {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) : B _⦋n⦌ :=
  B.map (transportSimplexFirstVertexMorphism σ).op (σ.obj 0).objDown.val

/-- 概要：初頂点の評価は元の底の全ての単体作用素と可換。
方針：初頂点座標の自然性と要素の圏の可換性を合成する。
規約：面と退化を同時に扱う。
使われ方：初頂点写像の単体的自然性。 -/
lemma transportSimplexFirstVertexSimplex_naturality {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n.len) :
    B.map α.op (transportSimplexFirstVertexSimplex σ) =
      transportSimplexFirstVertexSimplex ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) := by
  let τ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) m.len :=
    (SimplexCategory.toCat.map α).toFunctor ⋙ σ
  let f := σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))
  have hv : B.map f.down.hom (σ.obj 0).objDown.val = (τ.obj 0).objDown.val := f.down.map_val
  unfold transportSimplexFirstVertexSimplex
  rw [← hv]
  change (B.map (transportSimplexFirstVertexMorphism σ).op ≫ B.map α.op)
      (σ.obj 0).objDown.val =
    (B.map f.down.hom ≫ B.map (transportSimplexFirstVertexMorphism τ).op)
      (σ.obj 0).objDown.val
  rw [← B.map_comp, ← B.map_comp]
  exact congrArg (fun β ↦ B.map β.op (σ.obj 0).objDown.val)
    (transportSimplexFirstVertexMorphism_naturality α σ).symm

/-- 概要：単体圏の nerve から元の底への初頂点写像。
方針：各射列の初頂点評価と全単体作用素の自然性を束ねる。
規約：底の quasicategory 性は要求しない。
使われ方：全単体の切断の coherent な系を降ろす基底写像。 -/
def transportSimplexFirstVertexMap (B : SSet.{u}) : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) ⟶ B where
  app _ := ↾transportSimplexFirstVertexSimplex
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro σ
    exact (transportSimplexFirstVertexSimplex_naturality α.unop σ).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
