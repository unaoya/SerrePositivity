module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraRestrictionCoherence
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientSourceComparison

/-!
# 導来係数制限の恒等・合成比較

## 概要
HA §3.2.2 の係数制限の関手性を、既存の CAlg 上で示す。

## 方針
全ての厳密代数上で同じ比較を作り、局所化源での充満忠実性で降ろす。

## 規約
合成の比較の向きは界面に合わせる。

## 使われ方
M13 の係数制限の恒等・合成の欄。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]

/-- 厳密代数への自然同型を、元の全代数の局所化に写す。 -/
def algebraCAlgSourceNatIso (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]
    {F G : I ⥤ (operad A).Algebra} (η : F ≅ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap F ≫ algebraCAlgSource A) (nerveMap G ≫ algebraCAlgSource A) :=
  algebraCAlgSourceNatTransIso A η.hom fun i => by
    change QuasiIso ((Operad.Algebra.forget (operad A)).map (η.hom.app i))
    infer_instance

/-- 恒等環準同型による導来係数制限は恒等と自然同型。 -/
def barrattEcclesRestrict_id (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesRestrict (RingHom.id S)) (𝟙 (CAlg_R S)) := by
  apply algebraCAlgSource_descendIso S
  exact barrattEcclesRestrict_sourceIso (RingHom.id S) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (algebraCAlgSourceNatIso S (coefficientRestrictionIdIso S))
      rfl (by
        rw [show nerveMap (𝟭 (operad S).Algebra) = 𝟙 (nerve (operad S).Algebra) from
          nerveFunctor.map_id (Cat.of (operad S).Algebra), Category.id_comp, Category.comp_id])

/-- 環準同型の合成による導来係数制限は制限の合成と自然同型。 -/
def barrattEcclesRestrict_comp (f : S →+* T) (g : T →+* W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesRestrict (g.comp f))
      (barrattEcclesRestrict g ≫ barrattEcclesRestrict f) := by
  apply algebraCAlgSource_descendIso W
  let e := (barrattEcclesRestrict_sourceIso g).postcomp (barrattEcclesRestrict f)
  let d := (barrattEcclesRestrict_sourceIso f).precomp (nerveMap (coefficientRestriction g))
  exact barrattEcclesRestrict_sourceIso (g.comp f) ≪≫
    algebraCAlgSourceNatIso S (coefficientRestrictionCompIso f g) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d.symm rfl (by rw [Category.assoc]) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e.symm rfl (by rw [Category.assoc])

end SerrePositivity.EInfinity.BarrattEccles
