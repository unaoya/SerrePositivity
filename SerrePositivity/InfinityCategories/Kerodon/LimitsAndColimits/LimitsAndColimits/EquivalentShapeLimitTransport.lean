module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitExistence

/-!
概要：同値な添字に沿う制限は、元の同じ係数図式の極限の存在を保存し反映する。
方針：既存の回収の定理を指定同値の逆にも使い、元の可逆二胞体で図式を戻す。
規約：添字写像の単射性は仮定しない。
使われ方：Kerodon §7.1（Tag 02K2）、S8 の同じ left fibration の復元による係数移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ指定された同値な添字写像に沿って、極限の存在を双方向に移す。
Kerodon §7.1（Tag 02K2）、既存の回収の定理と図式同型の係数移送則。 -/
lemma hasLimit_iff_equivalentRestriction {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (hf : IsQCatEquivalence f) (F : B ⟶ X) :
    HasLimit F ↔ HasLimit (f ≫ F) := by
  constructor
  · intro hF
    obtain ⟨g, ⟨hfg⟩, ⟨hgf⟩⟩ := hf
    have hg : IsQCatEquivalence g := ⟨f, ⟨hgf⟩, ⟨hfg⟩⟩
    have he : HasLimit (g ≫ (f ≫ F)) ↔ HasLimit F := by
      simpa only [Category.assoc, Category.id_comp] using
        hasLimit_iff_of_functorIso (hgf.postcomp F)
    exact hasLimit_of_equivalentRestriction g hg (f ≫ F) (he.mpr hF)
  · exact hasLimit_of_equivalentRestriction f hf F

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
