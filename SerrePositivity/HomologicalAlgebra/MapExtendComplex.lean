module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive
import all Mathlib.Algebra.Homology.Embedding.Extend

/-!
概要：零射を保つ関手の複体への適用と、次数の埋め込みに沿う零延長の自然な交換。
方針：埋め込みの逆像が存在する次数では恒等同型、他の次数では零対象の同型を使う。
規約：完全性や有界性を要求しない。元の埋め込みと関手を保持する。
使われ方：HA 1.2.4、G10 の離散加群の二重複体と交代余面複体の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory Limits HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [HasZeroObject D]
variable (F : C ⥤ D) [F.Additive]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- 零延長の各場合での、元の関手による標準成分比較。 -/
def mapExtendComponent (K : HomologicalComplex C c) (i : Option ι) :
    F.obj (extend.X K i) ≅ extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero D)

/-- 各場合の成分比較は元の微分と可換。 -/
theorem mapExtendComponent_d (K : HomologicalComplex C c) (i j : Option ι) :
    (mapExtendComponent F K i).hom ≫ extend.d ((F.mapHomologicalComplex c).obj K) i j =
      F.map (extend.d K i j) ≫ (mapExtendComponent F K j).hom := by
  cases i <;> cases j <;> simp [mapExtendComponent, extend.d]

/-- 関手の適用と零延長を交換する複体の指定同型。 -/
def mapExtendIso (e : c.Embedding c') (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i => mapExtendComponent F K (e.r i))
    (fun i j _ => mapExtendComponent_d F K (e.r i) (e.r j))

/-- 成分比較は元の複体の射と自然。 -/
theorem mapExtendComponent_naturality {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i : Option ι) :
    F.map (extend.mapX f i) ≫ (mapExtendComponent F L i).hom =
      (mapExtendComponent F K i).hom ≫ extend.mapX ((F.mapHomologicalComplex c).map f) i := by
  cases i <;> simp [mapExtendComponent, extend.mapX]

/-- 複体の圏上での全関手の自然同型。 -/
def mapExtendNatIso (e : c.Embedding c') :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (mapExtendIso F e) (fun f => by
    ext i
    exact mapExtendComponent_naturality F f (e.r i))

end SerrePositivity.HomologicalAlgebra
