module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HeartFullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 導来 ∞ 圏の離散対象の特徴づけ

概要：零次以外のホモロジーが消える頂点は、その H⁰ の離散像と同型である。
方針：通常の導来圏の標準 t 構造を D3 の同値を通じて使い、同型を辺で表す。
規約：有界性の追加仮定は課さない。使われ方：D6 の離散入力の認識。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：離散頂点とは零次以外の Hⁱ がすべて零である頂点である。
方針：D3 の全整数次数のホモロジーで定義する。
規約：零次の値には条件を課さない。使われ方：離散対象の認識条件。 -/
def derivedInfinityDisc (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) : Prop :=
  ∀ i : ℤ, i ≠ 0 → IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i x)

/-- 概要：加群の離散埋め込みの像は零次以外のホモロジーが消える。
方針：単一複体との導来比較同型を通じてホモロジーの消滅を移す。
規約：任意の加群。使われ方：離散性の特徴づけの逆方向。 -/
theorem moduleHeartVertex_disc (M : ModuleCat.{u} S) :
    derivedInfinityDisc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartVertex S M) := by
  intro i hi
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat S) 0).obj M)) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
    · exact DerivedCategory.isZero_of_isLE _ 0 i h
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartDerivedIso S).app M))

/-- 概要：離散頂点の導来比較像は、その H⁰ の単一複体と同型である。
方針：標準 t 構造の上下零次の条件から単一複体を得て、H⁰ によって正規化する。
規約：H⁰ は D5d の関手。使われ方：J の像との比較。 -/
theorem derivedInfinityDisc_single (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (hx : derivedInfinityDisc x) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.obj ⟨x⟩ ≅
      (DerivedCategory.singleFunctor (ModuleCat S) 0).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x)) := by
  let X := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.obj ⟨x⟩
  have : X.IsGE 0 := (DerivedCategory.isGE_iff X 0).2 (fun i hi => hx i (by omega))
  have : X.IsLE 0 := (DerivedCategory.isLE_iff X 0).2 (fun i hi => hx i (by omega))
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
  let e₀ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x ≅ M :=
    (DerivedCategory.homologyFunctor (ModuleCat S) 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) 0).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat S) 0).mapIso e₀.symm⟩

/-- 概要：離散頂点 x は h D(S) で J(H⁰x) と同型である。
方針：単一複体との二つの同型を合成し、充満忠実な D3 の比較で持ち上げる。
規約：J は D5b と同じ解像度を使う。使われ方：離散対象の特徴づけの主定理。 -/
def derivedInfinityDiscIso (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (hx : derivedInfinityDisc x) :
    (⟨x⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartFunctor S).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.preimageIso
    ((Classical.choice (derivedInfinityDisc_single x hx)) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartDerivedIso S).symm.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x))

/-- 概要：離散対象の比較同型を表す一本の辺を選ぶ。
方針：二次切断のホモトピー圏の Hom の商の全射性を使う。
規約：始点は元の x、終点は選んだ J(H⁰x) の頂点。使われ方：単体的な同値の表示。 -/
def derivedInfinityDiscEdge (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (hx : derivedInfinityDisc x) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S))
      x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartVertex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x)) :=
  Classical.choose (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (derivedInfinityDiscIso x hx).hom)

/-- 概要：選んだ辺のホモトピー類は離散対象の比較同型の射である。
方針：商の全射性による選択の仕様を使う。
規約：同じ比較同型を表す。使われ方：辺の可逆性。 -/
lemma derivedInfinityDiscEdge_homMk (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (hx : derivedInfinityDisc x) :
    SSet.Truncated.HomotopyCategory₂.homMk (derivedInfinityDiscEdge x hx) =
      (derivedInfinityDiscIso x hx).hom :=
  Classical.choose_spec (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (derivedInfinityDiscIso x hx).hom)

/-- 概要：離散対象の比較辺は可逆である。
方針：h D(S) の同型を道によるホモトピー圏へ移す。
規約：Core の IsInvertibleEdge。使われ方：離散頂点と J(H⁰x) の辺による同値。 -/
theorem derivedInfinityDiscEdge_invertible (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (hx : derivedInfinityDisc x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (derivedInfinityDiscEdge x hx) := by
  have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk (derivedInfinityDiscEdge x hx)) := by
    rw [derivedInfinityDiscEdge_homMk]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (derivedInfinityDiscEdge x hx))

/-- 概要：離散性は h D(S) で J(H⁰x) と同型であることと同値である。
方針：主定理と、J の像のホモロジー消滅の同型不変性を使う。
規約：同型は存在命題としても取り出せる。使われ方：離散対象の認識。 -/
theorem derivedInfinityDisc_iff (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityDisc x ↔ Nonempty ((⟨x⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartFunctor S).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x)) := by
  refine ⟨fun hx => ⟨derivedInfinityDiscIso x hx⟩, ?_⟩
  rintro ⟨e⟩ i hi
  exact (moduleHeartVertex_disc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S x) i hi).of_iso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor S i).mapIso e)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
