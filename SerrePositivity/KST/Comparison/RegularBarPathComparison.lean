module

public import SerrePositivity.KST.Comparison.BasedPathEndpoint
public import SerrePositivity.KST.Comparison.ContractibleComparison
public import SerrePositivity.KST.Comparison.RegularBarContraction
public import SerrePositivity.KST.Comparison.GroupCompletionSpace
public import SerrePositivity.KST.Spectra.BoundaryFilling
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# 正則 bar の全空間と基点始点 path space の比較

概要：正則 bar の収縮を射影して path space へ送り、その写像の局所化可逆性を証明する。
方針：全空間の実際の収縮と、Kan な標的の path space の終射の単射 RLP を使う。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 のファイバーからループへの比較。
使われ方：標準群完備化写像のファイバー比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：正則 bar の収縮を Kan 置換した分類空間へ射影した区間の族。
方針：既存の収縮・射影・Kan 置換の単位を合成する。
規約：時刻零が基点、時刻一が bar 束の射影。
使われ方：基点始点 path space への転置。
-/
def regularBarPathFamily (M : SimplicialObject MonCat.{u}) :
    regularBar M ⊗ (Δ[1] : SSet.{u}) ⟶ (monoidBarKanPointed M).right :=
  regularBarContractionMap M ≫ regularBarProjection M ≫
    AnodyneKanReplacement.unit.app (monoidBar M)

/--
概要：正則 bar の射影した収縮は基点に始まる。
方針：収縮の零端点を射影し、モノイドの単位の基点を読む。
規約：基点は既存の monoidBarKanPointed のもの。
使われ方：path space へ curry する条件。
-/
theorem regularBarPathFamily_zero (M : SimplicialObject MonCat.{u}) :
    SSet.ι₀ ≫ regularBarPathFamily M =
      SSet.const (PointedSimplicialSet.basepoint (monoidBarKanPointed M)) := by
  unfold regularBarPathFamily
  rw [← Category.assoc, ← Category.assoc, regularBarContractionMap_zero,
    SSet.const_comp, SSet.const_comp]
  have hb : (regularBarProjection M).app (Opposite.op ⦋0⦌) (regularBarBasepoint M) =
      monoidBarBasepoint M := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  rw [hb]
  simp only [monoidBarKanPointed, PointedSimplicialSet.basepoint_ofVertex]
  rfl

/--
概要：正則 bar から Kan な分類空間の基点始点 path space への実際の比較。
方針：射影した収縮を始点固定の path の族へ転置する。
規約：モノイドの群状性はこの構成には不要。
使われ方：基点上のファイバーの比較。
-/
def regularBarPathMap (M : SimplicialObject MonCat.{u}) :
    regularBar M ⟶ (Spectra.basedPathSpace (monoidBarKanPointed M)).right :=
  basedPathFamilyMap (monoidBarKanPointed M) (regularBarPathFamily M) (regularBarPathFamily_zero M)

/--
概要：path space の終点は元の bar 束の射影の Kan 置換である。
方針：転置の終点評価と収縮の時刻一の式を使う。
規約：基底への射の厳密な可換性。
使われ方：二つのホモトピーファイバーの比較。
-/
theorem regularBarPathMap_endpoint (M : SimplicialObject MonCat.{u}) :
    regularBarPathMap M ≫ (Spectra.pathEndpoint (monoidBarKanPointed M)).right =
      regularBarProjection M ≫ AnodyneKanReplacement.unit.app (monoidBar M) := by
  rw [regularBarPathMap, basedPathFamilyMap_endpoint]
  unfold regularBarPathFamily
  rw [← Category.assoc, ← Category.assoc, regularBarContractionMap_one, Category.id_comp]

/--
概要：正則 bar の全空間の終射は局所化同型である。
方針：既存の実際の収縮を、選んだ基点への区間ホモトピーとして使う。
規約：元のモノイドの Kan 性は不要。
使われ方：可縮な全空間間の比較。
-/
theorem regularBar_terminal_localized_isIso (M : SimplicialObject MonCat.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from (regularBar M))) := by
  apply contractedSpace_terminal_localized_isIso (regularBar M) (regularBarBasepoint M)
  exact
    { h := regularBarContractionMap M
      h₀ := regularBarContractionMap_zero M
      h₁ := regularBarContractionMap_one M
      rel := by
        apply NatTrans.ext
        funext d
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }

/--
概要：正則 bar から基点始点 path space への比較は局所化同型。
方針：全空間の収縮と path space の終射の単射 RLP による二対三を使う。
規約：この全空間の比較には群状性は不要。
使われ方：群状性で得たホモトピーファイバーから loop への比較。
-/
theorem regularBarPathMap_localized_isIso (M : SimplicialObject MonCat.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (regularBarPathMap M)) := by
  apply map_between_contractible_localized_isIso (regularBarPathMap M)
    (regularBar_terminal_localized_isIso M)
  exact MonoRightLiftingContraction.localized_isIso _
    (Spectra.basedPathSpace_terminal_rlp (monoidBarKanPointed M))

end SerrePositivity.KST.Comparison
