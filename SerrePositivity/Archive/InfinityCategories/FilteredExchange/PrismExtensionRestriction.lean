module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：元の pointed な prism の延長空間と指定比較を任意の始域の族へ制限する。
方針：区間を保つ制限の可換正方形と可縮な延長空間の指定同型の自然性を使う。
規約：初期値と全区間を保持。使われ方：全空間と各点の持ち上げの比較を結ぶ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
/-- 概要：区間を保つ始域族の代入。方針：代入後に結合を戻す。
規約：元の全区間を保持。使われ方：延長の始域制限。 -/
def prismParameterRestriction {A C K : SSet.{u}} (s : C ⟶ A ⊗ K) :
    (Δ[1] : SSet.{u}) ⊗ C ⟶ (Δ[1] ⊗ A) ⊗ K :=
  (Δ[1] ◁ s) ≫ (α_ Δ[1] A K).inv

variable {A C E B K : SSet.{u}} (p : E ⟶ B)
  (b : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
  (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ b) (s : C ⟶ A ⊗ K)
local notation "i" => prismEndpoint 0 A ▷ K
local notation "h" => prismParameterRestriction s

/-- 概要：区間の始点を指定した元の prism の延長空間の実際の制限写像。
方針：同じ区間を保ち元の全始域族を s で制限する。
規約：底と初期値を厳密に保持。使われ方：各点の比較を同じ選択空間で読む。 -/
def prismExtensionRestriction :
    relativeFunctorExtensionSpace p b i v hv ⟶
      relativeFunctorExtensionSpace p (h ≫ b) (prismEndpoint 0 C) (s ≫ v)
        (by rw [Category.assoc, hv]; rfl) :=
  relativeExtensionRestriction p b i v hv h s (prismEndpoint 0 C) rfl

/-- 概要：prism 延長の元の指定同型は制限後の可縮な延長空間の指定同型に等しい。
方針：制限先での頂点間の射の一意性。
規約：同型の存在でなく指定値の等式。使われ方：全空間と各点の path 類の照合。 -/
lemma prismExtensionRestriction_vertexIso [LeftFibration p]
    (x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌) :
    VertexIso.map
      ((relativeFunctorExtensionSpace_isContractibleKan p b i
        (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K)
        v hv).vertexIso x y)
      (prismExtensionRestriction p b v hv s) =
        (relativeFunctorExtensionSpace_isContractibleKan p (h ≫ b) (prismEndpoint 0 C)
          (prismEndpoint_zero_leftAnodyne C) (s ≫ v) (by rw [Category.assoc, hv]; rfl)).vertexIso
          ((prismExtensionRestriction p b v hv s).app (Opposite.op ⦋0⦌) x)
          ((prismExtensionRestriction p b v hv s).app (Opposite.op ⦋0⦌) y) :=
  contractibleVertexIso_map _ _ (prismExtensionRestriction p b v hv s) x y

end SerrePositivity.InfinityCategories.F2
