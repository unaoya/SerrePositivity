module
public import SerrePositivity.InfinityCategories.Core.NestedCosliceIso

/-! # 任意の図式の二重 coslice

概要：coslice 内の任意の図式の下の coslice は、その図式を join で展開した coslice と同型である。
方針：join の結合同型で括弧を移し、任意パラメーターからの射の自然な同値を作る。
規約：値域に仮定は不要。使われ方：始対象から出る枝を余錐の条件から除く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：join へ展開した図式の下の図式を元の coslice 内の図式へ移す。
方針：join の括弧を右に寄せて curry し、左包含で図式 c が固定されることを示す。
規約：A は任意のパラメーター。使われ方：二重 coslice の比較の順方向。 -/
def diagramNestedCosliceDiagramCurry {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (A : SSet.{u})
    (F : {F : join (join K L) A ⟶ X // joinInl (join K L) A ≫ F = sliceUnderUncurry c}) :
    {G : join L A ⟶ sliceUnder p // joinInl L A ≫ G = c} := by
  let T := (stableJoinAssociator K L A).inv ≫ F.val
  have hT : joinInl K (join L A) ≫ T = p := by
    dsimp only [T]
    rw [← Category.assoc, stableJoinAssociator_leftLeft_inv, Category.assoc,
      F.property, sliceUnderUncurry_fixed c]
  refine ⟨sliceUnderCurry T hT, ?_⟩
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
  dsimp only [T]
  rw [← Category.assoc, stableJoinAssociator_inl_inv, F.property]

/-- 概要：元の coslice 内の図式をjoin へ展開した図式の下の図式へ戻す。
方針：uncurry して join の括弧を左に戻す。
規約：A は任意。使われ方：二重 coslice の比較の逆方向。 -/
def diagramNestedCosliceDiagramUncurry {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (A : SSet.{u})
    (G : {G : join L A ⟶ sliceUnder p // joinInl L A ≫ G = c}) :
    {F : join (join K L) A ⟶ X // joinInl (join K L) A ≫ F = sliceUnderUncurry c} :=
  ⟨(stableJoinAssociator K L A).hom ≫ sliceUnderUncurry G.val, by
    rw [← Category.assoc, stableJoinAssociator_inl, ← sliceUnderUncurry_precomp,
      G.property]⟩

/-- 概要：join へ展開した図式の下の図式と元の coslice 内の図式は同値。
方針：join の逆同型と curry・uncurry の逆則を合成する。
規約：A と値域は任意。使われ方：二重 coslice の単体集合の同型。 -/
def diagramNestedCosliceDiagramEquiv {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (A : SSet.{u}) :
    {F : join (join K L) A ⟶ X // joinInl (join K L) A ≫ F = sliceUnderUncurry c} ≃
      {G : join L A ⟶ sliceUnder p // joinInl L A ≫ G = c} where
  toFun := diagramNestedCosliceDiagramCurry c A
  invFun := diagramNestedCosliceDiagramUncurry c A
  left_inv F := by
    apply Subtype.ext
    dsimp only [diagramNestedCosliceDiagramUncurry, diagramNestedCosliceDiagramCurry]
    rw [sliceUnderUncurry_curry, Iso.hom_inv_id_assoc]
  right_inv G := by
    apply Subtype.ext
    apply sliceUnderUncurry_injective p
    dsimp only [diagramNestedCosliceDiagramCurry, diagramNestedCosliceDiagramUncurry]
    rw [sliceUnderUncurry_curry, Iso.inv_hom_id_assoc]


/-- 概要：二通りの coslice への任意パラメーターからの射は同値。
方針：coslice の普遍性の間に join の組み替えによる図式の同値を挟む。
規約：A は任意の単体集合。使われ方：二重 coslice の比較同型。 -/
def diagramNestedCosliceHomEquiv {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (A : SSet.{u}) :
    (A ⟶ sliceUnder (sliceUnderUncurry c)) ≃
      (A ⟶ sliceUnder c) :=
  (sliceUnderEquiv (sliceUnderUncurry c)).trans
    ((diagramNestedCosliceDiagramEquiv c A).trans
      (sliceUnderEquiv c).symm)

/-- 概要：二重 coslice の射の同値を二度 uncurry すると join の逆同型での前合成になる。
方針：curry・uncurry の逆則を二度使う。
規約：固定条件の証明に依存しない射の等式。
使われ方：比較同値のパラメーターに関する自然性。 -/
lemma diagramNestedCosliceHomEquiv_doubleUncurry {K L X A : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p)
    (f : A ⟶ sliceUnder (sliceUnderUncurry c)) :
    sliceUnderUncurry (sliceUnderUncurry (diagramNestedCosliceHomEquiv c A f)) =
      (stableJoinAssociator K L A).inv ≫ sliceUnderUncurry f := by
  let G := diagramNestedCosliceDiagramCurry c A ((sliceUnderEquiv (sliceUnderUncurry c)) f)
  change sliceUnderUncurry (sliceUnderUncurry (sliceUnderCurry G.val G.property)) = _
  rw [sliceUnderUncurry_curry]
  dsimp only [G, diagramNestedCosliceDiagramCurry, sliceUnderEquiv]
  rw [sliceUnderUncurry_curry]
  rfl

/-- 概要：二重 coslice の射の同値はパラメーターの前合成に関して自然。
方針：二度 uncurry し、join の逆結合同型の自然性で比較する。
規約：f と g は任意の単体的な射。使われ方：同値を実際の同型として表す。 -/
lemma diagramNestedCosliceHomEquiv_naturality {K L X A B : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (f : A ⟶ B) (g : B ⟶ sliceUnder (sliceUnderUncurry c)) :
    diagramNestedCosliceHomEquiv c A (f ≫ g) = f ≫ diagramNestedCosliceHomEquiv c B g := by
  apply sliceUnderUncurry_injective c
  apply sliceUnderUncurry_injective p
  rw [diagramNestedCosliceHomEquiv_doubleUncurry,
    sliceUnderUncurry_precomp (diagramNestedCosliceHomEquiv c B g) f,
    sliceUnderUncurry_precomp (sliceUnderUncurry (diagramNestedCosliceHomEquiv c B g))
      (joinMap (𝟙 L) f), diagramNestedCosliceHomEquiv_doubleUncurry,
    sliceUnderUncurry_precomp g f]
  have h := stableJoinAssociator_inv_naturality (𝟙 K) (𝟙 L) f
  simpa only [joinMap_id, Category.assoc] using
    congrArg (fun e ↦ e ≫ sliceUnderUncurry g) h.symm

/-- 概要：展開した図式の下の coslice は元の coslice 内で図式の下の coslice と同型。
方針：任意パラメーターからの射の自然な同値を恒等射に適用する。
規約：追加の仮定なし。使われ方：S4 の最初の固定因子を忘れる制限の比較。 -/
def diagramNestedCosliceIso {K L X : SSet.{u}} {p : K ⟶ X} (c : L ⟶ sliceUnder p) :
    sliceUnder (sliceUnderUncurry c) ≅ sliceUnder c where
  hom := diagramNestedCosliceHomEquiv c _ (𝟙 _)
  inv := (diagramNestedCosliceHomEquiv c _).symm (𝟙 _)
  hom_inv_id := by
    apply (diagramNestedCosliceHomEquiv c (sliceUnder (sliceUnderUncurry c))).injective
    rw [diagramNestedCosliceHomEquiv_naturality, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := diagramNestedCosliceHomEquiv_naturality c
      ((diagramNestedCosliceHomEquiv c _).symm (𝟙 _)) (𝟙 (sliceUnder (sliceUnderUncurry c)))
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm


end SerrePositivity.InfinityCategories
