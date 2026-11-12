module
public import SerrePositivity.KST.SConstruction.CoherentStringNativeMaps
public import SerrePositivity.KST.SConstruction.CoherentStringFullPaths
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 元の coherent 図式からの端点固定の全合成列の native Hom 族
概要：元の図式の全合成列を、追加の円柱入力なしに一つの native Hom の単体射へ束ねる。
方針：精密化の高次 Path 単体を最後の元の豊穣作用で評価し、二つの自然性を合成する。
規約：元の頂点と豊穣作用を保持し、局所 Kan 性も新しい代表の選択も要求しない。
使われ方：元の K prism の長辺から各合成への全パラメータの実円柱を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の全合成列と全精密化の評価を、一つの固定端点の native Hom の実族へ束ねる。 -/
def coherentArrowNativeFamily
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶
      SimplicialCategory.sHom (coherentStringVertexObject Q x)
        (coherentStringVertexObject Q y) where
  app n := ↾fun F => (coherentStringNativeMap Q (F.obj (Fin.last n.unop.len))).app n
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag F)
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ θ
    apply ConcreteCategory.hom_ext
    intro F
    let a := F.map (homOfLE (Fin.le_last (θ.unop.toOrderHom (Fin.last m))))
    have h₁ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (coherentStringNativeMap_naturality Q a) (Opposite.op ⦋m⦌))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag ((nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)).map θ F))
    have h₂ := congrArg ((coherentStringNativeMap Q (F.obj (Fin.last n))).app (Opposite.op ⦋m⦌))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag_naturality F θ.unop)
    have h₃ := NatTrans.naturality_apply (coherentStringNativeMap Q (F.obj (Fin.last n))) θ
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag F)
    exact h₁.symm.trans (h₂.trans h₃)

/-- 全合成列の実族の元の射の頂点での値。 -/
def coherentArrowNativeInitialVertex
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    (SimplicialCategory.sHom (coherentStringVertexObject Q x)
      (coherentStringVertexObject Q y)) _⦋0⦌ :=
  (coherentArrowNativeFamily Q f).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))

/-- 元の射の頂点から全合成列の実評価へ向かう、端点固定 Hom 内の全パラメータの円柱。 -/
def coherentArrowNativeContraction
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (coherentArrowNativeInitialVertex Q f)) (coherentArrowNativeFamily Q f) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (coherentArrowStringContraction f)
    (coherentArrowNativeFamily Q f)
  refine
    { h := H.h
      h₀ := H.h₀.trans ?_
      h₁ := H.h₁.trans (Category.id_comp _)
      rel := H.rel }
  exact SSet.const_comp _ _

/-- 全合成列族の元の頂点では、同じ元の合成列の全頂点 Path の評価を回収する。 -/
lemma coherentArrowNativeFamily_vertex
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    (coherentArrowNativeFamily Q f).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      (coherentStringNativeMap Q s).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath s)) := by
  change (coherentStringNativeMap Q s).app _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) = _
  rw [coherentStringPathFlag_vertex]

/-- 初点は、元の図式の同じ射の二端点だけの Path の豊穣評価そのもの。 -/
lemma coherentArrowNativeInitialVertex_endpoint
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    coherentArrowNativeInitialVertex Q f =
      (coherentStringNativeMap Q (coherentArrowStringDirect f)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath
          (show (ULift.up 0 : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide))) := by
  rw [coherentArrowNativeInitialVertex, coherentArrowNativeFamily_vertex,
    coherentStringFullPath_direct]

end SerrePositivity.KST.SConstruction
