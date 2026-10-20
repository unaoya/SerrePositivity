module

public import SerrePositivity.InfinityCategories.F1B.KanFunctorHomotopyClasses
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowIdentityComposition

/-!
概要：元の円柱の逆同型の代表を先に選び、後から前合成した場合の射の類を計算する。
方針：h Fun の前合成関手が同型の逆を保つことを使う。
規約：代表を選ぶ順序を保つ。使われ方：共通 path end が実際に使う逆円柱の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の逆代表へ前合成した射の類は、前合成した元の円柱の同型の逆である。 -/
lemma homotopyPrecompInverse_hom {A B X : SSet.{u}} [KanComplex X]
    {f g : B ⟶ X} (H : SSet.Homotopy f g) (i : A ⟶ B) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPrecomp
        (FunctorIso.simplicialHomotopy (functorIsoOfSimplicialHomotopy H).symm) i)) =
      (functorIsoOfSimplicialHomotopy (functorHomotopyPrecomp H i)).inv := by
  let I := functorIsoOfSimplicialHomotopy H
  let F := (hoFunctor.map ((pre i).app X)).toFunctor
  apply (cancel_mono (functorIsoOfSimplicialHomotopy (functorHomotopyPrecomp H i)).hom).mp
  rw [Iso.inv_hom_id]
  change _ ≫ SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i)) = _
  rw [functorHomotopyPrecomp_hom, functorHomotopyPrecomp_hom,
    kanFunctorIso_simplicialHomotopy_hom]
  change F.map I.inv ≫ F.map I.hom = 𝟙 _
  rw [← F.map_comp, I.inv_hom_id, F.map_id]

end SerrePositivity.InfinityCategories.HomotopyLimits
