module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedCosliceReindex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoconeMappingPiZeroChoice

/-! # 固定図式上の再添字付けの Hom への作用

概要：余錐空間の再添字付けは、余極限頂点の標準自己同型による Hom の前合成として表される。
方針：coslice の自己射に対する自然性と余錐の選択変更の公式を合成する。
規約：形状の自己射は図式を保つ対合。使われ方：対称 span の交換作用を写像空間で読む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：図式を固定した形状の自己射で余錐を同じ coslice 内で再添字付けする。
方針：coslice の自己射を零単体へ適用する。
規約：余錐の頂点は保たれる。使われ方：同じ図式の二つの普遍余錐の比較。 -/
def JoinCocone.reindexFixed {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (i : K ⟶ K) (hi : i ≫ p = p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex p i hi).app (Opposite.op ⦋0⦌) c

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.JoinCocone (reindexFixed)


/-- 概要：固定図式上の再添字付けは余錐頂点を保つ。
方針：coslice の自己射と終点射影の可換性を頂点で評価する。
規約：実際の頂点の等号。使われ方：標準比較を自己同型にする終点の表示変更。 -/
lemma JoinCocone.vertex_reindexFixed {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (i : K ⟶ K) (hi : i ≫ p = p) : (c.reindexFixed i hi).vertex = c.vertex :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex_projection p i hi)
    (Opposite.op ⦋0⦌)) c

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.JoinCocone (vertex_reindexFixed)


/-- 概要：図式を固定する形状の対合は余錐の余極限性を保つ。
方針：coslice の再添字付け同型が始対象性を保存することを使う。
規約：値域の quasicategory 性は不要。使われ方：交換後の標準余錐比較。 -/
lemma IsColimitCone.reindexFixed {K X : SSet.{u}} {p : K ⟶ X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : K ⟶ K) (hi : i ≫ p = p) (hii : i ≫ i = 𝟙 K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.reindexFixed i hi) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindexIso p i hi hii).hom c).1 hc

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsColimitCone (reindexFixed)


/-- 概要：固定図式上の形状の対合は余極限頂点の標準自己同型を与える。
方針：元の余錐と再添字付け後の余錐の標準比較を、同じ頂点の表示へ戻す。
規約：X は quasicategory。使われ方：余錐空間の再添字付けの Hom への作用。 -/
def fixedCoconeReindexVertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : K ⟶ K) (hi : i ≫ p = p)
    (hii : i ≫ i = 𝟙 K) :
    (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso c (c.reindexFixed i hi) hc (hc.reindexFixed i hi hii) ≪≫
    eqToIso (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_reindexFixed i hi))

/-- 概要：固定図式の再添字付けの余錐空間への作用は標準頂点自己同型による前合成。
方針：同じ底上の coslice の自己射に対する自然性と、余極限余錐の変更を合成する。
規約：X は quasicategory、c は余極限余錐。使われ方：二枝交換を Hom の自己作用で読む。 -/
lemma coconeMappingSpacePiZeroEquiv_reindexFixed {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : K ⟶ K)
    (hi : i ≫ p = p) (hii : i ≫ i = 𝟙 K) (y : X _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex p i hi y) a) =
      (fixedCoconeReindexVertexIso c hc i hi hii).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y a := by
  have hn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex p i hi) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex_projection p i hi)
    c hc (c.reindexFixed i hi) (hc.reindexFixed i hi hii) rfl y a
  change eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
    (c.vertex_reindexFixed i hi).symm) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv (c.reindexFixed i hi) (hc.reindexFixed i hi hii) y
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex p i hi y) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y a at hn
  have ht := congrArg (fun t => eqToHom (congrArg
    (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_reindexFixed i hi)) ≫ t) hn
  simp only [eqToHom_refl, Category.id_comp] at ht
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpacePiZeroEquiv_change_cocone c (c.reindexFixed i hi) hc
    (hc.reindexFixed i hi hii), ht]
  simp only [fixedCoconeReindexVertexIso, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.assoc, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
