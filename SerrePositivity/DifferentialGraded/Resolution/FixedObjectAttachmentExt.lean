module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapLaws
public import SerrePositivity.DifferentialGraded.Resolution.InitialStageComparison

/-!
概要：同じ全境界 cell 付加上の増大比較を、元 Hom と新生成元で判定する。
方針：元の cell 付加の dg 関手普遍性を固定対象表示へ戻す。
規約：全次数 Hom の厳密等号であり、増大後の等号や導来等号ではない。
使われ方：D-8 e の固定分解作用の恒等・合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  {E : Type w} [DGCategory A E]
  {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E}
local notation "SI" => @FixedObjectAugmentation.CellIndex A _ D D dD id S
local notation "SC" => @FixedObjectAugmentation.cells A _ D D dD id S

def attachedSourceFunctor (M : Map S.attach T F) :
    letI : DGCategory A D := S.category; DGFunctor A ((SC).Objects A D SI) T.Objects := by
  let obj := F.obj
  let m := M.hom
  have hi := M.map_id
  have hc := M.map_comp
  letI : DGCategory A D := S.category
  exact
    { obj := fun x => ⟨obj x.val⟩
      map x y := m x.val y.val
      map_id x := hi x.val
      map_comp x y z := hc x.val y.val z.val }

lemma attached_hom_ext (M N : Map S.attach T F)
    (ht : ∀ x y, S.transition x y ≫ M.hom x y = S.transition x y ≫ N.hom x y)
    (hg : ∀ i : S.CellIndex,
      (M.hom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) =
        (N.hom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i)) (x y : D) :
    M.hom x y = N.hom x y := by
  have he : attachedSourceFunctor M = attachedSourceFunctor N := by
    let L := attachedSourceFunctor M
    let R := attachedSourceFunctor N
    let t := S.transition
    let m := M.hom
    let n := N.hom
    let : DGCategory A D := S.category
    apply (SC).functor_ext A D SI L R
    · apply EnrichedFunctor.ext (Complex A)
        (F := (SC).restrictFunctor A D SI L) (G := (SC).restrictFunctor A D SI R)
        (fun _ => rfl)
      intro a b
      change (t a b ≫ m a b) ≫ eqToHom (by rfl) = t a b ≫ n a b
      rw [eqToHom_refl, Category.comp_id]
      exact ht a b
    · apply heq_of_eq
      funext i
      exact hg i
  let : DGCategory A D := S.category
  exact eq_of_heq (DGFunctor.hcongr_map he ⟨x⟩ ⟨y⟩)

end SerrePositivity.DifferentialGraded.FixedObjectAugmentation.Map
