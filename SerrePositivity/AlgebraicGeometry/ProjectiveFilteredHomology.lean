module

public import SerrePositivity.AlgebraicGeometry.ModuleCatFilteredExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
概要：加群の filtered 余極限と各次数のコホモロジーを比較する。
方針：短複体を関手圏で作り、AB5 による余極限の完全性を使う。
規約：増大完全性の同値から正次数の H の同型を推論しない。
使われ方：有限被覆の Čech 計算と Noether 近似の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]

local instance projectiveFilteredHomologyExactColimits :
    HasExactColimitsOfShape J (ModuleCat.{u} R) :=
  moduleCatFiltered_hasExactColimitsOfShape R J
variable (S : J ⥤ ShortComplex (ModuleCat.{u} R))

/-- 短複体の filtered 図式を、関手圏の一つの短複体にまとめる。 -/
def projectiveFilteredShortComplexDiagram : ShortComplex (J ⥤ ModuleCat.{u} R) :=
  (ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.obj S

/-- 関手圏の短複体のコホモロジーは、有限段ごとのコホモロジーの図式と一致する。 -/
def projectiveFilteredShortComplexHomologyDiagramIso :
    (projectiveFilteredShortComplexDiagram S).homology ≅
      S ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun j ↦ ((projectiveFilteredShortComplexDiagram S).mapHomologyIso
      ((evaluation J (ModuleCat.{u} R)).obj j)).symm) (by
        intro i j f
        change (projectiveFilteredShortComplexDiagram S).homology.map f ≫
            ((projectiveFilteredShortComplexDiagram S).mapHomologyIso
              ((evaluation J (ModuleCat.{u} R)).obj j)).inv =
          ((projectiveFilteredShortComplexDiagram S).mapHomologyIso
            ((evaluation J (ModuleCat.{u} R)).obj i)).inv ≫
              ShortComplex.homologyMap ((projectiveFilteredShortComplexDiagram S).mapNatTrans
                ((evaluation J (ModuleCat.{u} R)).map f))
        rw [ShortComplex.homologyMap_mapNatTrans]
        simp only [Iso.inv_hom_id_assoc]
        rfl)

/-- 短複体の filtered 余極限のコホモロジーは、各段のコホモロジーの余極限。
Čech 版の近似比較（原典 Stacks 30.6.1 の Hⁱ）への加群圏の計算。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveFilteredShortComplexHomologyIso :
    ((projectiveFilteredShortComplexDiagram S).map (colim (J := J))).homology ≅
      colimit (S ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R)) :=
  (projectiveFilteredShortComplexDiagram S).mapHomologyIso (colim (J := J)) ≪≫
    (colim (J := J)).mapIso (projectiveFilteredShortComplexHomologyDiagramIso S)

variable (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

/-- 複体の余極限の短複体と、各項の余極限を取った短複体との比較。 -/
def projectiveFilteredComplexShortComplexIso (n : ℕ) :
    (projectiveFilteredShortComplexDiagram
      (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n)).map
        (colim (J := J)) ≅ (colimit F).sc n := by
  let p := (ComplexShape.up ℕ).prev n
  let q := (ComplexShape.up ℕ).next n
  let V := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ)
  let S := projectiveFilteredShortComplexDiagram
    (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n)
  let compare (i : ℕ) := preservesColimitIso (V i) F
  refine ShortComplex.isoMk (compare p).symm (compare n).symm (compare q).symm ?_ ?_
  · apply colimit.hom_ext
    intro j
    change colimit.ι (F ⋙ V p) j ≫ (compare p).inv ≫ (colimit F).d p n =
      colimit.ι (F ⋙ V p) j ≫ colim.map S.f ≫ (compare n).inv
    rw [colimit.ι_map_assoc]
    change colimit.ι (F ⋙ V p) j ≫ (compare p).inv ≫ (colimit F).d p n =
      (F.obj j).d p n ≫ colimit.ι (F ⋙ V n) j ≫ (compare n).inv
    simp only [compare, ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv]
    exact (colimit.ι F j).comm p n
  · apply colimit.hom_ext
    intro j
    change colimit.ι (F ⋙ V n) j ≫ (compare n).inv ≫ (colimit F).d n q =
      colimit.ι (F ⋙ V n) j ≫ colim.map S.g ≫ (compare q).inv
    rw [colimit.ι_map_assoc]
    change colimit.ι (F ⋙ V n) j ≫ (compare n).inv ≫ (colimit F).d n q =
      (F.obj j).d n q ≫ colimit.ι (F ⋙ V q) j ≫ (compare q).inv
    simp only [compare, ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv]
    exact (colimit.ι F j).comm n q

/-- 複体の filtered 余極限と各次数のコホモロジーとの同型。
Čech 版の近似比較（原典 Stacks 30.6.1 の Hⁱ）への加群圏の計算。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveFilteredComplexHomologyIso (q : ℕ) :
    (colimit F).homology q ≅
      colimit (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) :=
  (ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso
      (projectiveFilteredComplexShortComplexIso F q).symm ≪≫
    projectiveFilteredShortComplexHomologyIso
      (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q)

end SerrePositivity.AlgebraicGeometry
