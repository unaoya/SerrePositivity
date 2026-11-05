module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponentLaws
public import SerrePositivity.InfinityCategories.F1.KanModels.KanDiagramComponentPointHom

/-! # Kan 値の coherent 図式の指定同型を、各元の標準値で評価する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.KanModels
open SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {F G H : I ⥤ KanObject.{u}}

/-- 任意の指定 coherent 同型を、同じ元の標準 Kan 値の成分へ正規化する。 -/
def kanDiagramValueIso (e : FunctorIso (kanDiagramCoherentNerve F)
    (kanDiagramCoherentNerve G)) (i : I) :
    VertexIso (spaceInfinityVertex (F.obj i)) (spaceInfinityVertex (G.obj i)) :=
  (eqToIso (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex F i))).symm ≪≫
    e.app (ULift.up (nerveVertex i)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex G i))

/-- 元の標準値への正規化も、指定した二つの同型の合成を保つ。 -/
theorem kanDiagramValueIso_trans
    (e : FunctorIso (kanDiagramCoherentNerve F) (kanDiagramCoherentNerve G))
    (f : FunctorIso (kanDiagramCoherentNerve G) (kanDiagramCoherentNerve H)) (i : I) :
    kanDiagramValueIso (e ≪≫ f) i = kanDiagramValueIso e i ≪≫ kanDiagramValueIso f i := by
  apply Iso.ext
  simp [kanDiagramValueIso, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_trans, Category.assoc]

/-- 元の標準値への正規化は、同じ指定同型の逆を保つ。 -/
theorem kanDiagramValueIso_symm
    (e : FunctorIso (kanDiagramCoherentNerve F) (kanDiagramCoherentNerve G)) (i : I) :
    kanDiagramValueIso e.symm i = (kanDiagramValueIso e i).symm := by
  apply Iso.ext
  simp [kanDiagramValueIso, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_symm, Category.assoc]

/-- 元の点ごとの変換では、同じ指定成分の標準値表示そのものを回収する。 -/
theorem kanDiagramValueIso_pointwise {F G : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) (i : I) :
    kanDiagramValueIso (kanDiagramFunctorIsoOfPointwise η hη) i =
      kanDiagramComponentValueIso η hη i := rfl

end SerrePositivity.InfinityCategories.F1.KanModels

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso_pointwise := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso_pointwise

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso_symm := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso_symm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso_trans := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso_trans

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso._proof_2 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramValueIso.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso.eq_1
