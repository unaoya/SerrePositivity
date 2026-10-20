module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UpperMissingCube
public import SerrePositivity.InfinityCategories.Coherent.PathNerve

/-!
概要：指定した合成面を一つ欠く Path の Hom の部分単体集合と Kan 延長。
方針：元の内部点座標の同型で上面を欠く立方体の結果を移す。
規約：包含方向の Path を使う。使われ方：外側ホーンの二つの未知 Hom の第一段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
open CategoryTheory.SimplicialThickening
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 元の Path の内部点座標で、指定合成面を一つ欠く部分を定義する。 -/
def upperMissingPath (hab : a < b) (i : Set.Ioo a b) :
    (nerve (Path a b)).Subcomplex :=
  (upperMissingCube i).preimage (pathInteriorNerveIso hab).hom

/-- 全零座標面と指定外の合成面による、元の Path の所属条件。 -/
lemma mem_upperMissingPath_iff (hab : a < b) (i : Set.Ioo a b)
    {n : SimplexCategoryᵒᵖ} (F : (nerve (Path a b)).obj n) :
    F ∈ (upperMissingPath hab i).obj n ↔
      (∃ x : Set.Ioo a b, x.1 ∉ (F.obj (Fin.last n.unop.len)).I) ∨
        ∃ x : Set.Ioo a b, x ≠ i ∧ x.1 ∈ (F.obj 0).I := by
  change ((pathInteriorNerveIso hab).hom.app n F) ∈ (upperMissingCube i).obj n ↔ _
  exact mem_upperMissingCube_endpoints_iff i ((pathInteriorNerveIso hab).hom.app n F)

/-- 同じ内部点座標で、Path の既知部分の包含も anodyne。 -/
lemma upperMissingPath_anodyne (hab : a < b) (i : Set.Ioo a b) :
    SSet.anodyneExtensions (upperMissingPath hab i).ι :=
  anodyne_subcomplexPreimage (pathInteriorNerveIso hab) _ (upperMissingCube_anodyne i)

/-- Path の既知部分を保持して、元の全 Hom 上へ Kan 延長する。 -/
lemma upperMissingPath_extension (hab : a < b) (i : Set.Ioo a b)
    {X : SSet.{u}} [KanComplex X] (f : (upperMissingPath hab i : SSet) ⟶ X) :
    ∃ g : nerve (Path a b) ⟶ X, (upperMissingPath hab i).ι ≫ g = f := by
  have : HasLiftingProperty (upperMissingPath hab i).ι (terminal.from X) :=
    upperMissingPath_anodyne hab i _ (by rwa [← fibration_iff])
  let sq : CommSq f (upperMissingPath hab i).ι (terminal.from X) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
