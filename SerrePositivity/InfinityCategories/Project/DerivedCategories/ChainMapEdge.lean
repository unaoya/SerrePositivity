module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexEdgeCalculus
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology

/-! # 鎖写像による D(S) の辺とホモロジー

概要：semifree 複体の鎖写像を D(S) の辺へ移し、その Hⁱ は通常のホモロジー射であることを示す。
方針：閉零 cochain と辺の同値を用い、既存のホモロジー比較の自然性を評価する。
規約：元の頂点の表記を固定する。使われ方：D6a の四辺、heart の射と H⁰ の両立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex

open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}

/-- 概要：二頂点の複体間の鎖写像は、その頂点間の D(S) の辺を与える。
方針：鎖写像の閉次数零 cochain を辺へ移す。
規約：頂点は定値頂点に置換しない。使われ方：指定射の H⁰ を評価する。 -/
def derivedChainMapEdge (f : (x.obj 0).val ⟶ (y.obj 0).val) :
    SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle ⟨Cochain.ofHom f, δ_ofHom f⟩

/-- 概要：鎖写像の D(S) の辺を全複体へ包含すると通常の complexEdge の一単体になる。
方針：充満包含の Hom 写像は恒等なので成分を評価する。
規約：元の二頂点の表記には依存しない。使われ方：指定された四辺の一致。 -/
lemma derivedChainMapEdge_inclusion (f : (x.obj 0).val ⟶ (y.obj 0).val) :
    ((derivedChainMapEdge f).map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

/-- 概要：D(S) の鎖写像の辺を包含して読み戻すと元の鎖写像になる。
方針：一単体の一致から鎖写像を同定する。
規約：元の二頂点の複体を始域・終域とする。使われ方：ホモロジー比較の自然性。 -/
lemma derivedChainMapEdge_chainMap (f : (x.obj 0).val ⟶ (y.obj 0).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((derivedChainMapEdge f).map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))
      = f :=
  eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derived_edgeChainMap_heq_complexEdge _ f (derivedChainMapEdge_inclusion f))

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：鎖写像の辺の Hⁱ は元の鎖写像のホモロジー射と両立する。
方針：包含からの読み戻しを既存の自然性に代入する。
規約：すべての整数次数。使われ方：D6 の列の射を頂点と辺の Hⁱ で読む。 -/
lemma derivedChainMapEdge_homology (i : ℤ) (f : (x.obj 0).val ⟶ (y.obj 0).val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap S i (derivedChainMapEdge f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i y).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i x).hom ≫ HomologicalComplex.homologyMap f i := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso_naturality S i (derivedChainMapEdge f)
  rw [derivedChainMapEdge_chainMap] at h
  exact h

/-- 概要：鎖写像の辺の次数零の射は D5d の H⁰ と両立する。
方針：全次数の自然性を零次で評価する。
規約：D5d の同じ射と同じ比較同型。使われ方：指定四辺の H⁰ の厳密な整合。 -/
lemma derivedChainMapEdge_hZero (f : (x.obj 0).val ⟶ (y.obj 0).val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S (derivedChainMapEdge f) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S x).hom ≫ HomologicalComplex.homologyMap f 0 :=
  derivedChainMapEdge_homology 0 f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
