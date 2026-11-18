module

public import SerrePositivity.InfinityCategories.Sheaves.SheafSiteEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EquivalenceAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.EquivalenceInverseSquare

/-!
概要：site 同値に沿う層化の全関手比較を、二つの指定反射の随伴から作る。
方針：層の包含の可換正方形を指定逆へ移し、その mate の可逆性を使う。
  文献対応：HTT 6.2.2.7、Kerodon §6.1.3（Tag 02D4）の随伴の全自然比較。
規約：同じ指定反射を使う。単位との照合は後続の法則として別に保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- site 同値に沿う層化の比較。任意の前層と全高次単体を同時に比較する。 -/
def sheafificationReindexFunctorIso (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E) :
    FunctorIso (sheafificationFunctor K hK ≫ reindexPresheafFunctor e.functor)
      (reindexPresheafFunctor e.functor ≫ sheafificationFunctor J hJ) := by
  let t := (reindexPresheafFunctor_isQCatEquivalence (E := E) e).choose
  let s := (reindexSheafFunctor_isQCatEquivalence (E := E) e J K hf hg).choose
  let rC := Classical.choice hJ
  let rD := Classical.choice hK
  have hsquare : FunctorIso (sheafInclusion K ≫ t.hom)
      (s.hom ≫ sheafInclusion J) :=
    eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f))
      (reindexSheafFunctor_comp e J K hf).symm)
  let hright := functorIsoInverseSquare s t (sheafInclusion K) (sheafInclusion J) hsquare
  let a := (equivalenceAdjunction t).comp rC.adjunction
  let b := rD.adjunction.comp (equivalenceAdjunction s)
  let hleft := adjointFunctorIsoOfRightIso a b hright
  have h := (hleft.postcomp (sheafInclusion J)).symm
  change FunctorIso ((rD.reflector ≫ sheafInclusion K) ≫ t.hom)
    (t.hom ≫ (rC.reflector ≫ sheafInclusion J))
  have hscomp : s.hom ≫ sheafInclusion J = sheafInclusion K ≫ t.hom :=
    reindexSheafFunctor_comp e J K hf
  simpa only [Category.assoc, hscomp] using h

end SerrePositivity.InfinityCategories.Sheaves
