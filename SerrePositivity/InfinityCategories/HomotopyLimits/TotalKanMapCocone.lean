module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConstantCoconeHomotopyComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMapCocone

/-!
概要：元の余極限 Kan 模型の射を、元の単位を使う native 余錐全体へ移す。
方針：指定射へ元の全空間の単位を前合成し、頂点表示の標準等式だけを続ける。
規約：Kan 射の辺に沿う native 余錐輸送との同定は別。使われ方：両脚の単位表現の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})

/-- 元の余極限 Kan 射に元の全空間の単位を前合成した、指定頂点の値への射。 -/
def totalKanMapCoconeInput (a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G) :
    smallLeftUnstraightening F ⟶ (spaceInfinityObject (F2.coherentDiagramTotalVertex G)).obj :=
  F2.continuousKanReplacementUnit.app (smallLeftUnstraightening F) ≫ a ≫
    eqToHom (F2.coherentDiagramTotalVertex_object G).symm

/-- 元の Kan 射の単位表現から実現した、同じ図式上の native 余錐。 -/
def totalKanMapCocone (a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G) :
    JoinCocone F :=
  F2.coherentConstantCocone F (F2.coherentDiagramTotalVertex G) (totalKanMapCoconeInput F G a)

/-- 単位表現の余錐の頂点は、標的図式の元の余極限頂点。 -/
lemma totalKanMapCocone_vertex (a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G) :
    (totalKanMapCocone F G a).vertex = F2.coherentDiagramTotalVertex G :=
  F2.coherentConstantCocone_vertex _ _ _

/-- 元の全空間射の Kan 置換にホモトピックなら、単位表現の全余錐は元の写像余錐と同型。 -/
def totalKanMapCoconeIso
    {a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G}
    (m : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
    (H : SSet.Homotopy a (F2.continuousKanReplacement.map m)) :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      (F2.coconeMappingPointAt (totalKanMapCocone F G a) (F2.coherentDiagramTotalVertex G)
        (totalKanMapCocone_vertex F G a))
      (F2.coconeMappingPointAt (F2.coherentTotalMapCocone F G m) (F2.coherentDiagramTotalVertex G)
        (F2.coherentTotalMapCocone_vertex F G m)) := by
  let T := functorHomotopyPostcomp
    (functorHomotopyPrecomp H
      (F2.continuousKanReplacementUnit.app (smallLeftUnstraightening F)))
    (eqToHom (F2.coherentDiagramTotalVertex_object G).symm)
  have ht : (F2.continuousKanReplacementUnit.app (smallLeftUnstraightening F) ≫
      F2.continuousKanReplacement.map m) ≫
        eqToHom (F2.coherentDiagramTotalVertex_object G).symm =
      m ≫ F2.coherentDiagramTotalUnit G := by
    rw [← F2.continuousKanReplacementUnit.naturality m]
    rfl
  let U : SSet.Homotopy (totalKanMapCoconeInput F G a) (m ≫ F2.coherentDiagramTotalUnit G) :=
    { h := T.h, h₀ := T.h₀, h₁ := T.h₁.trans ht, rel := T.rel }
  exact constantCoconeHomotopyIso F (F2.coherentDiagramTotalVertex G) U

end SerrePositivity.InfinityCategories.HomotopyLimits
