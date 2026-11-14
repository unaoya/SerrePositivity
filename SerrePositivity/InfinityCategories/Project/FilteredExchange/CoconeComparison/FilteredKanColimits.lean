module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
概要：Kan 複体の通常の filtered 余極限は Kan 複体。
方針：ホーンの有限表示性で一段へ因子分解し、そこで得た充填を余極限へ送る。
規約：通常の小圏による strict 図式を扱い、∞ 余極限との比較は別に証明する。
使われ方：filtered 余極限の具体的な Kan 模型と有限図式の因子分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：全ての値が Kan である filtered 図式の余極限余錐の頂点は Kan。
方針：ホーンを一段に下ろして充填し、元の余極限余錐の脚で戻す。
規約：選ばれた colimit だけでなく任意の実際の余極限余錐に適用する。
使われ方：具体的な filtered 余極限模型の充填性。 -/
lemma kanComplex_of_filtered_isColimit {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ SSet.{u}} [∀ i, KanComplex (F.obj i)] {c : Cocone F} (hc : IsColimit c) :
    KanComplex c.pt := by
  rw [KanComplex.iff]
  intro n i fs hf
  obtain ⟨j, t, ht⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc hf.desc
  obtain ⟨g, hg⟩ := KanComplex.hornFilling t
  have hfill : (horn (n + 1) i).ι ≫ (g ≫ c.ι.app j) = hf.desc := by
    rw [← Category.assoc, ← hg, ht]
  refine ⟨g ≫ c.ι.app j, fun k hk ↦ ?_⟩
  rw [← horn.ι_ι_assoc i k hk, hfill]
  exact hf.ι_desc k hk

/-- 概要：選ばれた通常の filtered 余極限は Kan 複体。
方針：その余極限余錐に一般の Kan 判定を適用する。
規約：∞ 余極限性はこの instance からは主張しない。
使われ方：filtered 図式に追加の Kan 置換を使わない具体的な模型。 -/
instance filteredColimit_kanComplex {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ SSet.{u}) [∀ i, KanComplex (F.obj i)] : KanComplex (colimit F) :=
  kanComplex_of_filtered_isColimit (colimit.isColimit F)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
