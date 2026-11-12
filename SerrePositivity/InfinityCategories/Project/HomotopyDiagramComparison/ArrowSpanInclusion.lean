module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpan

/-!
# 両脚の射の類を広げる元の三本矢の包含

概要：指定する両脚の射の類の包含から、同じ三本矢の充満忠実な包含を作る。
方針：元の対象と三射を保ち、所属の証明だけを移す。
規約：中間射・左右の縦射・全可換条件を変更しない。
使われ方：特殊な三本矢・片脚が自明な三本矢・弱同値の三本矢の比較。
-/

@[expose] public section
universe u v
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {C : Type u} [Category.{v} C] {L R L' R' : MorphismProperty C}
  {X Y : C}

/-- 両脚の類を広げる同じ元の三本矢の包含。 -/
def inclusion (hL : L ≤ L') (hR : R ≤ R') : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L' R' X Y where
  obj S := ⟨S.left, S.right, S.leftMap, S.middle, S.rightMap,
    hL _ S.left_mem, hR _ S.right_mem⟩
  map f := ⟨f.left, f.right, f.left_w, f.middle_w, f.right_w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance inclusion_faithful (hL : L ≤ L') (hR : R ≤ R') :
    (inclusion (X := X) (Y := Y) hL hR).Faithful where
  map_injective := by
    intro S T f g h
    let J := inclusion (X := X) (Y := Y) hL hR
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext f g (congrArg (fun k : J.obj S ⟶ J.obj T => k.left) h)
      (congrArg (fun k : J.obj S ⟶ J.obj T => k.right) h)

instance inclusion_full (hL : L ≤ L') (hR : R ≤ R') :
    (inclusion (X := X) (Y := Y) hL hR).Full where
  map_surjective f := ⟨⟨f.left, f.right, f.left_w, f.middle_w, f.right_w⟩, rfl⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
