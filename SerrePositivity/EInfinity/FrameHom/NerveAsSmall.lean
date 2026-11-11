module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 対象と Hom の宇宙を同時に揃えた nerve の元の比較

概要：AsSmall の nerve を元の nerve の単体の ULift と実同型で比較する。
方針：元の射列の up・down と全作用素との交換を使う。
規約：元の対象・射・単体を保持し、圏の同値だけから同型を推論しない。
使われ方：分解の comma の可縮性を F1b の同じ宇宙の小圏へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.EInfinity.FrameHom.NerveAsSmall

open CategoryTheory
open SerrePositivity.SimplicialModel

variable (C : Type u) [Category.{v} C]

/-- 概要：元の AsSmall の up の後の down は恒等（Low 命題 3.6）。
方針：元の対象・射の ULift の順逆を評価する。
規約：元の関手の厳密な等式。
使われ方：nerve の宇宙比較の逆則。 -/
lemma up_down : AsSmall.up.{v, u, w} (C := C) ⋙ AsSmall.down = 𝟭 C := rfl

/-- 概要：元の AsSmall の down の後の up も恒等（Low 命題 3.6）。
方針：元の対象・射の ULift の eta 則を使う。
規約：同じ持ち上げた圏を使う。
使われ方：nerve の宇宙比較の逆則。 -/
lemma down_up : AsSmall.down.{v, u, w} (C := C) ⋙ AsSmall.up = 𝟭 (AsSmall.{w} C) := rfl

/-- 概要：AsSmall の nerve は元の nerve の ULift と実同型（Low 命題 3.6）。
方針：元の射列の全対象・全射を up・down する。
規約：順射は元の射列の down の持ち上げ。
使われ方：同じ全単体の可縮性の宇宙調整。 -/
def iso : nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) where
  hom :=
    { app _ := ↾fun c => ULift.up (c ⋙ AsSmall.down.{v, u, w})
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun c => c.down ⋙ AsSmall.up.{v, u, w}
      naturality _ _ _ := rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro c
    change (c ⋙ AsSmall.down.{v, u, w}) ⋙ AsSmall.up = c
    rw [CategoryTheory.Functor.assoc, down_up, CategoryTheory.Functor.comp_id]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    change (c.down ⋙ AsSmall.up.{v, u, w}) ⋙ AsSmall.down = c.down
    rw [CategoryTheory.Functor.assoc, up_down, CategoryTheory.Functor.comp_id]

/-- 概要：元の nerve の終射の反転性は AsSmall 後も成立（Low 命題 3.6）。
方針：同じ比較同型・元の終射の ULift・標準零単体の宇宙比較を合成する。
規約：大きい宇宙にも単体集合モデルは要求しない。
使われ方：F1b の小圏の comma の弱可縮性。 -/
lemma terminal_localized_isIso
    (hC : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve C)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (AsSmall.{w} C)))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{w, max u v}.map
      (SSet.stdSimplex.isTerminalObj₀.from (nerve C)))) :=
    UniverseLift.anodyneQ_map_isIso_of_small _ hC
  have h : (iso C).hom ≫ SSet.uliftFunctor.map
      (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso (SimplexCategory.mk 0)).hom =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (AsSmall.{w} C)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← h, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.FrameHom.NerveAsSmall
