module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardSegmentMarked
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedGeneratorColumns

/-!
# 自由圏の元の forward 区間の指定性の完全な判定

概要：区間合成が指定射列であることと、その区間の全列が指定射列であることを同定する。
方針：自由射列の連結の指定性と元の一列の前後での分割を使う。
規約：元の全射列を保持し、後置部分の指定性を入力にしない。
使われ方：語の fiber 内の最初の非指定列の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Segment
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} (S : Zigzag W.paths w X Y)
  (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward)

lemma forward_path_map_mem_iff : W.paths (map .forward S p q hpq hd) ↔
    ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → W.paths (S.arrow i) := by
  constructor
  · intro hm i hi hi'
    rw [forward_map_split_column S p q hpq hd i hi hi'] at hm
    have hm := (W.comp_mem_paths_iff.1 (W.comp_mem_paths_iff.1 hm).2).1
    change W.paths (eqToHom _ ≫ S.arrow i ≫ eqToHom _) at hm
    exact (Direction.transport_mem _ _ _).1 hm
  · exact forward_map_mem S p q hpq hd W.paths

end SerrePositivity.EInfinity.Hammock.Segment
