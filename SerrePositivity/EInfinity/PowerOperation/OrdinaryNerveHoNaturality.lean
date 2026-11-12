module

public import SerrePositivity.EInfinity.PowerOperation.OrdinaryNerveHomotopyFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
# 同じ通常関手と nerve のホモトピー圏の自然な比較

DAG XIII §2.2 の全始域比較の補助。元の射列と同じ一次単体の端点輸送を使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open scoped Simplicial
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

def ordinaryNerveHoNaturality (F : C ⥤ D) :
    ordinaryNerveHomotopyFunctor C ⋙ (hoFunctor.map (nerveMap F)).toFunctor ≅
      F ⋙ ordinaryNerveHomotopyFunctor D :=
  NatIso.ofComponents
    (fun X => eqToIso (congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F X)))
    (fun {X Y} f => by
      let hx := congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F X)
      let hy := congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F Y)
      have h := MorphismSpaces.homMk_transport (nerveMap_app_mk₀ F X) (nerveMap_app_mk₀ F Y)
        (((nerve.edgeMk f).map (nerveMap F)).toTruncated)
        (nerve.edgeMk (F.map f)).toTruncated (nerveMap_app_mk₁ F f)
      change SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map (nerveMap F)) ≫
        (eqToIso hy).hom = (eqToIso hx).hom ≫ SSet.HomotopyCategory.homMk (nerve.edgeMk (F.map f))
      apply (cancel_epi (eqToIso hx).inv).mp
      simpa only [hx, hy, SSet.HomotopyCategory.homMk, Category.assoc,
        Iso.inv_hom_id_assoc, eqToIso.hom, eqToIso.inv,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using h)

end SerrePositivity.EInfinity.PowerOperation
