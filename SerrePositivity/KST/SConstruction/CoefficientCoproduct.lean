module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts

/-! # 係数の直和の実際の単体集合
概要：単体集合族の次数ごとの直和を実際の余積として構成する。
方針：単体作用素は添字を保存し、係数にのみ作用する。
規約：添字と係数の宇宙をそろえる。使われ方：要素の圏の二重単体解消の行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet

/-- 係数族の直和。添字を保存したまま単体作用素を作用させる。 -/
def coefficientCoproduct {I : Type u} (A : I → SSet.{u}) : SSet.{u} where
  obj n := Σ i, (A i).obj n
  map h := ↾fun s => ⟨s.1, (A s.1).map h s.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro s
    simp
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro s
    simp

/-- 各係数から直和への標準包含。 -/
def coefficientCoproductInclusion {I : Type u} (A : I → SSet.{u}) (i : I) :
    A i ⟶ coefficientCoproduct A where
  app _ := ↾fun x => ⟨i, x⟩
  naturality {_n _m} _h := rfl

/-- 次数ごとの直和を頂点に持つ余錐。 -/
def coefficientCoproductCofan {I : Type u} (A : I → SSet.{u}) : Cofan A :=
  Cofan.mk (coefficientCoproduct A) (coefficientCoproductInclusion A)

/-- 次数ごとの直和は単体集合の圏でも余積。 -/
def coefficientCoproductIsColimit {I : Type u} (A : I → SSet.{u}) :
    IsColimit (coefficientCoproductCofan A) := by
  refine Cofan.IsColimit.mk _ (fun s => ?_) ?_ ?_
  · exact { app := fun n => ↾fun x => (s.inj x.1).app n x.2
            naturality := fun {n m} h => by
              apply ConcreteCategory.hom_ext
              intro x
              exact ConcreteCategory.congr_hom ((s.inj x.1).naturality h) x.2 }
  · intro s i
    rfl
  · intro s m h
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (h i) n) x

/-- 係数ごとの射は直和の射を誘導する。 -/
def coefficientCoproductMap {I : Type u} {A B : I → SSet.{u}} (f : ∀ i, A i ⟶ B i) :
    coefficientCoproduct A ⟶ coefficientCoproduct B where
  app n := ↾fun x => ⟨x.1, (f x.1).app n x.2⟩
  naturality {n m} h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (Sigma.mk x.1) (ConcreteCategory.congr_hom ((f x.1).naturality h) x.2)

/-- 係数ごとの局所化同型は実際の直和の局所化同型を与える。 -/
lemma coefficientCoproductMap_localized_isIso {I : Type u} {A B : I → SSet.{u}}
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (f i))) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (coefficientCoproductMap f)) := by
  apply SerrePositivity.SimplicialModel.KanLocalizedCoproducts.actual_localized_isIso I f hf
    (coefficientCoproductCofan A) (coefficientCoproductCofan B)
    (coefficientCoproductIsColimit A) (coefficientCoproductIsColimit B)
  intro i
  rfl

end SerrePositivity.KST.SConstruction
