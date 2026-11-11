module
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionImageClosed
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroNaturality

/-!
概要：同じ全多次数の wide 成分を元の三角圏 K₀ の余核へ写す。
方針：cofiber が本質像に入る辺の両端は K₀ の余核で等しいことを使う。
規約：成分集合との全単射や K₀ 単射性は未証明のまま主張しない。
使われ方：離散的障害と元の K₀ 商群との同定の順方向。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の同じ反復 S 射の三角圏 K₀ の余核。
方針：誘導準同型の像で標的 K₀ を割る。
規約：本質像の対象だけで生成した未検証の代替群へ置き換えない。
使われ方：wide 成分からの障害写像の標的。 -/
abbrev completionKZeroCokernel (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) : Type u :=
  TriangulatedK0 (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) ⧸
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range

/-- 概要：元の標的頂点の K₀ 余核類。
方針：同じ頂点のホモトピー圏の対象類を余核へ射影する。
規約：wide に属するかどうかに依存せず元の頂点を評価する。
使われ方：辺不変性を示して成分へ降ろす元の評価。 -/
def completionKZeroVertexClass (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (y : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋0⦌) :
    completionKZeroCokernel r ι f :=
  QuotientAddGroup.mk (TriangulatedK0.mk (HomotopyCategory.mk y))

/-- 概要：元の本質像の頂点の K₀ 余核類は零。
方針：像の頂点同型を対象類の等号へ移し、誘導準同型の像であることを示す。
規約：本質像所属から出発し、K₀ の逆向きの像検出は仮定しない。
使われ方：分母辺の cofiber 項を余核で消去する。 -/
lemma completionKZeroVertexClass_zero_of_image (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (y : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋0⦌)
    (hy : y ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) :
    completionKZeroVertexClass r ι f y = 0 := by
  obtain ⟨x, ⟨e⟩⟩ := hy
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨TriangulatedK0.mk (HomotopyCategory.mk x), ?_⟩
  exact (triangulatedKZeroSourceMap_mk (((multiSEndofunctor r).obj ι).map f)
    (HomotopyCategory.mk x)).trans (TriangulatedK0.mk_iso e)

/-- 概要：wide の元の分母辺の両端は K₀ 余核で等しい。
方針：同じ実 cofiber の完全三角形の関係を余核へ写し、その像項を消去する。
規約：辺の像条件と元の対象類を保持する。
使われ方：成分集合への障害写像の降下条件。 -/
lemma completionKZeroVertexClass_edge (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    {x y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌}
    (a : SSet.Edge x y) :
    completionKZeroVertexClass r ι f x.val = completionKZeroVertexClass r ι f y.val := by
  have ha : a.edge.val ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) := by
    simpa only [op_id, CategoryTheory.Functor.map_id, types_id_apply]
      using a.edge.property (𝟙 ⦋1⦌)
  obtain ⟨q, z, hz, ⟨e⟩⟩ := ha
  have hc := square_bottom_vertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a.edge.val) q.square q.bottom_edge
  have hs := hc.1.trans (congrArg Subtype.val a.src_eq)
  have ht := hc.2.trans (congrArg Subtype.val a.tgt_eq)
  have hq := TriangulatedK0.mk_triangle (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle q.toZeroTriangle q.isPushout)
    ⟨q.toZeroTriangle, q.isPushout, ⟨Iso.refl _⟩⟩
  change TriangulatedK0.mk
      (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex q.square 1 0)) =
    TriangulatedK0.mk (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex q.square 0 0)) +
    TriangulatedK0.mk (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
      (HomotopyCategory.mk q.cofiber) at hq
  have hq' := hs ▸ ht ▸ hq
  have hz' : q.cofiber ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val := by
    obtain ⟨s, ⟨es⟩⟩ := hz
    exact ⟨s, ⟨es ≪≫ e.symm⟩⟩
  let π := QuotientAddGroup.mk'
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range
  have h := congrArg π hq'
  rw [map_add] at h
  change completionKZeroVertexClass r ι f y.val =
    completionKZeroVertexClass r ι f x.val + completionKZeroVertexClass r ι f q.cofiber at h
  exact ((by simpa only [completionKZeroVertexClass_zero_of_image r ι f q.cofiber hz',
    add_zero] using h) : completionKZeroVertexClass r ι f y.val =
      completionKZeroVertexClass r ι f x.val).symm

/-- 概要：元の wide 模型の成分集合から元の K₀ 余核への障害写像。
方針：辺で不変な頂点の余核類を成分集合へ降ろす。
規約：全単射性は別工程であり、この定義には仮定しない。
使われ方：離散的障害の商群同定の実比較射。 -/
def completionWideKZeroObstruction (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) → completionKZeroCokernel r ι f :=
  SSet.π₀.lift (fun x => completionKZeroVertexClass r ι f x.val)
    (fun {_ _} a => completionKZeroVertexClass_edge r ι f a)

end SerrePositivity.KST.SConstruction.Cofinality
