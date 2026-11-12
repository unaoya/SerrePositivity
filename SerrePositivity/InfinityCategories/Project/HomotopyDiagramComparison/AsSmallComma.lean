module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# 宇宙を揃えた元の関手の comma 圏の比較

概要：AsSmall の前後で同じ comma 圏を全対象・全射の圏同値で比較する。
方針：元の可換三角形の対象・射を up・down して充満忠実性と本質的全射性を示す。
規約：元の関手の作用を保持し、全ての宇宙を同じ上限へ持ち上げる。
使われ方：分解の元の comma の可縮性を F1b の小圏の判定へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v' w

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (d : D)

/-- 概要：元の関手の対象と Hom の宇宙を同じ上限へ揃える（Low 命題 3.6）。
方針：元の down・関手・up を合成する。
規約：元の対象と射への作用を保持する。
使われ方：F1b の同じ宇宙の小圏の比較関手。 -/
def smallFunctor : AsSmall.{max w u' v'} C ⥤ AsSmall.{max w u v} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- 概要：持ち上げた関手は元の全対象・全射への作用を厳密に保持（Low 命題 3.6）。
方針：up の後の down を評価する。
規約：元の関手と同じ up を使う。
使われ方：宇宙調整後の余終性を元の分解図式へ接続する。 -/
lemma smallFunctor_up : AsSmall.up ⋙ smallFunctor.{u, v, u', v', w} F = F ⋙ AsSmall.up := rfl

/-- 概要：持ち上げた関手の comma を元の comma の持ち上げへ送る（Low 命題 3.6）。
方針：元の可換三角形を down し、その comma 対象を up する。
規約：全ての可換単体作用素を保持する。
使われ方：元の comma の可縮性の宇宙調整。 -/
def comparison : CostructuredArrow (smallFunctor.{u, v, u', v', w} F) (AsSmall.up.obj d) ⥤
    AsSmall.{max w u v u' v'} (CostructuredArrow F d) where
  obj s := AsSmall.up.obj (CostructuredArrow.mk (Y := (AsSmall.down.obj s.left)) s.hom.down)
  map θ := AsSmall.up.map (CostructuredArrow.homMk θ.left.down
    (congrArg ULift.down (CostructuredArrow.w θ)))
  map_id s := by
    apply ULift.ext
    exact CostructuredArrow.hom_ext _ _ rfl
  map_comp θ φ := by
    apply ULift.ext
    exact CostructuredArrow.hom_ext _ _ rfl

/-- 概要：comma の宇宙比較は元の射を区別する（Low 命題 3.6）。
方針：射の左成分の down を回収する。
規約：射を同型類へ落とさない。
使われ方：元の comma 表示の圏同値。 -/
instance comparison_faithful : (comparison.{u, v, u', v', w} F d).Faithful where
  map_injective {s t} θ φ h := by
    apply CostructuredArrow.hom_ext
    apply ULift.ext
    exact congrArg (fun k => k.down.left) h

/-- 概要：comma の宇宙比較は全可換三角形を回収する（Low 命題 3.6）。
方針：元の左成分と可換条件を up する。
規約：同じ元の射を使う。
使われ方：元の comma 表示の充満性。 -/
instance comparison_full : (comparison.{u, v, u', v', w} F d).Full where
  map_surjective {s t} θ := by
    let k : s ⟶ t := CostructuredArrow.homMk (ULift.up θ.down.left) (by
      apply ULift.ext
      exact CostructuredArrow.w θ.down)
    exact ⟨k, by apply ULift.ext; exact CostructuredArrow.hom_ext _ _ rfl⟩

/-- 概要：元の全 comma 対象は持ち上げた関手の comma から来る（Low 命題 3.6）。
方針：元の対象と構造射を up し、同じ左対象の恒等同型で比較する。
規約：元の構造射を変更しない。
使われ方：元の comma 表示の本質的全射性。 -/
instance comparison_essSurj : (comparison.{u, v, u', v', w} F d).EssSurj where
  mem_essImage c := by
    let c₀ : CostructuredArrow F d := ULift.down c
    let s : CostructuredArrow (smallFunctor.{u, v, u', v', w} F) (AsSmall.up.obj d) :=
      CostructuredArrow.mk (Y := AsSmall.up.obj c₀.left) (AsSmall.up.map c₀.hom)
    let e : ULift.down ((comparison F d).obj s) ≅ c₀ :=
      CostructuredArrow.isoMk (Iso.refl c₀.left) (by
        change F.map (𝟙 c₀.left) ≫ c₀.hom = c₀.hom
        rw [F.map_id, Category.id_comp])
    exact ⟨s, ⟨AsSmall.up.mapIso e⟩⟩

/-- 概要：同じ comma 圏の AsSmall 前後の実際の圏同値（Low 命題 3.6）。
方針：元の比較関手の充満忠実性と本質的全射性を束ねる。
規約：順関手は元の down と up の comparison。
使われ方：元の comma の可縮性と小圏の slice 判定の接続。 -/
def equivalence : CostructuredArrow (smallFunctor.{u, v, u', v', w} F) (AsSmall.up.obj d) ≌
    AsSmall.{max w u v u' v'} (CostructuredArrow F d) := by
  let : (comparison.{u, v, u', v', w} F d).IsEquivalence := {}
  exact (comparison F d).asEquivalence

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma
