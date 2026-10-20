module

public import SerrePositivity.InfinityCategories.F1.StrictTransportEnrichedFunctor
public import SerrePositivity.InfinityCategories.F1.KanDiagramSimplicialCategory

/-!
概要：strict transport の像の豊穣圏を全 Kan 値通常図式へ含める。
方針：像条件だけを忘れ、各 Hom の射は恒等にする。
規約：全 Kan 図式の strict な Hom の Kan 性は主張しない。
使われ方：復元 span と weighted nerve の共同比較を独立な依存で束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：strict transport の像の図式を全 strict Kan 図式へ含める。
方針：対象の像条件を忘れ、変換空間には恒等写像を作用させる。
規約：Hom の Kan 性を全図式へ移す主張は含まない。
使われ方：Kerodon §5.3.1、weighted nerve 後の図式の共同実現。 -/
def strictTransportKanDiagramEnriched {C : Type u} [Category.{u} C] :
    EnrichedFunctor SSet.{u} (StrictTransportDiagramObject C) (KanDiagramObject C) where
  obj F := ⟨F.val, trivial⟩
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [Category.comp_id, tensorHom_id]
    rfl

end SerrePositivity.InfinityCategories
