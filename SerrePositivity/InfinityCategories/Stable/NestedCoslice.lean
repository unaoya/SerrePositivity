module
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorBoundary
public import SerrePositivity.InfinityCategories.Stable.Cocone
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-! # 余錐の下の二重 coslice の比較

概要：余錐全体の下の図式を、元の coslice 内で余錐頂点の下の図式へ移す。
方針：join の結合同型と coslice の普遍性を使う。
規約：値域には quasicategory 性を仮定しない。
使われ方：S4 の余極限頂点の付加と coslice の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：結合同型の逆と左の二因子の包含は可換。
方針：順方向の包含の式に逆同型を合成する。
規約：射の厳密な等式。使われ方：二重 coslice の固定条件。 -/
lemma stableJoinAssociator_inl_inv (K L M : SSet.{u}) :
    joinMap (𝟙 K) (joinInl L M) ≫ (stableJoinAssociator K L M).inv =
      joinInl (join K L) M := by
  rw [← stableJoinAssociator_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：最初の因子の包含は結合同型の逆で二つの左包含になる。
方針：順方向を合成して、左包含と joinMap の可換性を使う。
規約：K からの射。使われ方：元の図式 p の固定条件。 -/
lemma stableJoinAssociator_leftLeft_inv (K L M : SSet.{u}) :
    joinInl K (join L M) ≫ (stableJoinAssociator K L M).inv =
      joinInl K L ≫ joinInl (join K L) M := by
  apply (cancel_mono (stableJoinAssociator K L M).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    stableJoinAssociator_inl, joinInl_joinMap, Category.id_comp]

/-- 概要：結合同型の逆も三因子の射に関して自然。
方針：順方向の自然性を逆同型で移す。
規約：任意の三因子の射。使われ方：二重 coslice のパラメーター自然性。 -/
lemma stableJoinAssociator_inv_naturality {K K' L L' M M' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    joinMap f (joinMap g h) ≫ (stableJoinAssociator K' L' M').inv =
      (stableJoinAssociator K L M).inv ≫ joinMap (joinMap f g) h := by
  apply (cancel_mono (stableJoinAssociator K' L' M').hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    stableJoinAssociator_naturality, Iso.inv_hom_id_assoc]

/-- 概要：余錐全体の下の図式を元の coslice 内の図式へ移す。
方針：join の括弧を右に寄せて curry し、左包含で余錐 c が固定されることを示す。
規約：A は任意のパラメーター。使われ方：二重 coslice の比較の順方向。 -/
def nestedCosliceDiagramCurry {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (A : SSet.{u})
    (F : {F : join (join K Δ[0]) A ⟶ X // joinInl (join K Δ[0]) A ≫ F = c.val}) :
    {G : join Δ[0] A ⟶ sliceUnder p // joinInl Δ[0] A ≫ G = SSet.yonedaEquiv.symm c} := by
  let T := (stableJoinAssociator K Δ[0] A).inv ≫ F.val
  have hT : joinInl K (join Δ[0] A) ≫ T = p := by
    dsimp only [T]
    rw [← Category.assoc, stableJoinAssociator_leftLeft_inv, Category.assoc,
      F.property, c.property]
  refine ⟨sliceUnderCurry T hT, ?_⟩
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry, sliceUnderUncurry_yoneda]
  dsimp only [T]
  rw [← Category.assoc, stableJoinAssociator_inl_inv, F.property]

/-- 概要：元の coslice 内の図式を余錐全体の下の図式へ戻す。
方針：uncurry して join の括弧を左に戻す。
規約：A は任意。使われ方：二重 coslice の比較の逆方向。 -/
def nestedCosliceDiagramUncurry {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (A : SSet.{u})
    (G : {G : join Δ[0] A ⟶ sliceUnder p // joinInl Δ[0] A ≫ G = SSet.yonedaEquiv.symm c}) :
    {F : join (join K Δ[0]) A ⟶ X // joinInl (join K Δ[0]) A ≫ F = c.val} :=
  ⟨(stableJoinAssociator K Δ[0] A).hom ≫ sliceUnderUncurry G.val, by
    rw [← Category.assoc, stableJoinAssociator_inl, ← sliceUnderUncurry_precomp,
      G.property, sliceUnderUncurry_yoneda]⟩

/-- 概要：余錐全体の下の図式と元の coslice 内の図式は同値。
方針：join の逆同型と curry・uncurry の逆則を合成する。
規約：A と値域は任意。使われ方：二重 coslice の単体集合の同型。 -/
def nestedCosliceDiagramEquiv {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (A : SSet.{u}) :
    {F : join (join K Δ[0]) A ⟶ X // joinInl (join K Δ[0]) A ≫ F = c.val} ≃
      {G : join Δ[0] A ⟶ sliceUnder p // joinInl Δ[0] A ≫ G = SSet.yonedaEquiv.symm c} where
  toFun := nestedCosliceDiagramCurry c A
  invFun := nestedCosliceDiagramUncurry c A
  left_inv F := by
    apply Subtype.ext
    dsimp only [nestedCosliceDiagramUncurry, nestedCosliceDiagramCurry]
    rw [sliceUnderUncurry_curry, Iso.hom_inv_id_assoc]
  right_inv G := by
    apply Subtype.ext
    apply sliceUnderUncurry_injective p
    dsimp only [nestedCosliceDiagramCurry, nestedCosliceDiagramUncurry]
    rw [sliceUnderUncurry_curry, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
