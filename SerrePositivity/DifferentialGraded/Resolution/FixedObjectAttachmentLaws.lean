module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectAttachmentExt

/-!
概要：同じ全境界 cell 付加は増大比較の恒等・合成を厳密に保つ。
方針：元 Hom と指定境界 cell の生成元で全 Hom を判定する。
規約：増大の後での一致に弱めず、元の attachedHom 自体の等号を証明する。
使われ方：D-8 e の指定 cell 分解作用の段階帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

private lemma dependent_apply_heq {α : Sort*} {β : α → Sort*} (f : ∀ a, β a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

lemma attach_identity (S : FixedObjectAugmentation A D D id) :
    (identity S).attach = identity S.attach := by
  apply map_ext
  funext x y
  apply attached_hom_ext
  · intro a b
    change S.transition a b ≫ (identity S).attachedHom a b = S.transition a b ≫ 𝟙 _
    rw [transition_attachedHom]
    change 𝟙 _ ≫ S.transition a b = S.transition a b ≫ 𝟙 _
    simp
  · intro i
    change ((identity S).attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) = _
    rw [attachedHom_cellGenerator]
    exact eq_of_heq (dependent_apply_heq S.cellGenerator (identity_cellMap S i))

variable {E : Type w} [DGCategory A E] [Small.{u} E]
  {B : Type z} [DGCategory A B] [Small.{u} B]

lemma attach_composition {S : FixedObjectAugmentation A D D id}
    {T : FixedObjectAugmentation A E E id} {U : FixedObjectAugmentation A B B id}
    {F : DGFunctor A D E} {G : DGFunctor A E B} (M : Map S T F) (N : Map T U G) :
    (composition M N).attach = composition M.attach N.attach := by
  apply map_ext
  funext x y
  apply attached_hom_ext
  · intro a b
    change S.transition a b ≫ (composition M N).attachedHom a b =
      S.transition a b ≫ (M.attachedHom a b ≫ N.attachedHom (F.obj a) (F.obj b))
    rw [transition_attachedHom, ← Category.assoc, transition_attachedHom,
      Category.assoc, transition_attachedHom]
    change (M.hom a b ≫ N.hom (F.obj a) (F.obj b)) ≫ _ = _
    rw [Category.assoc]
    rfl
  · intro i
    change ((composition M N).attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) =
      (N.attachedHom (F.obj i.1) (F.obj i.2.1)).f i.2.2.degree
        ((M.attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i))
    rw [attachedHom_cellGenerator, M.attachedHom_cellGenerator]
    have hn := N.attachedHom_cellGenerator (M.cellMap i)
    change (N.attachedHom (F.obj i.1) (F.obj i.2.1)).f i.2.2.degree
      (T.cellGenerator (M.cellMap i)) = U.cellGenerator (N.cellMap (M.cellMap i)) at hn
    rw [hn]
    exact eq_of_heq (dependent_apply_heq U.cellGenerator (composition_cellMap M N i))

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
