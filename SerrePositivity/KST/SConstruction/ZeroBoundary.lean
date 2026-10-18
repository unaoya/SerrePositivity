module
public import SerrePositivity.KST.SConstruction.ZeroDirectionsRanges
public import SerrePositivity.KST.SConstruction.ZeroDirectionsWeak
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! # 零方向の境界の有限合併の弱可縮性
概要：個々の零方向の像の有限合併も anodyne 局所化で一点と同値。
方針：交差の厳密な計算と部分複体の合併の pushout を用いて帰納する。
規約：非空の方向の合併に適用する。使われ方：fat wedge 全体を自然に潰す処理。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：非空の零方向の像から一点への射は局所化で可逆。
方針：単射の源と range の同型を通じて実現の弱可縮性を移す。
規約：部分複体の像そのものについての主張。使われ方：有限合併の初期段階。 -/
lemma zeroDirectionsRange_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (zeroDirectionsRange s X : SSet.{u}))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let a := Subcomplex.toRange (zeroDirectionsInclusion s X)
  have ha : IsIso (Q.map a) := inferInstance
  have hh : IsIso (Q.map a ≫ Q.map (toUnit (zeroDirectionsRange s X : SSet.{u}))) := by
    have he : a ≫ toUnit (zeroDirectionsRange s X : SSet.{u}) =
        toUnit (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X)) := isTerminalTensorUnit.hom_ext _ _
    rw [← Q.map_comp, he]
    exact zeroDirectionsRealization_toPoint_localized_isIso s hs X
  exact (isIso_comp_left_iff _ _).1 hh

/-- 概要：部分複体の交差は二つの部分複体の合併に分配する。
方針：各次数の集合の論理式を比較する。
規約：追加の格子 instance は導入しない。使われ方：境界交差の有限帰納。 -/
lemma subcomplex_inf_sup {W : SSet.{u}} (A B C : W.Subcomplex) :
    A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) := by
  ext d x
  change (x ∈ A.obj d ∧ (x ∈ B.obj d ∨ x ∈ C.obj d)) ↔
    ((x ∈ A.obj d ∧ x ∈ B.obj d) ∨ (x ∈ A.obj d ∧ x ∈ C.obj d))
  tauto

/-- 概要：二つの弱可縮な部分複体の交差も弱可縮なら合併も弱可縮。
方針：部分複体の合併の pushout を一点の pushout と cube で比較する。
規約：Kan 性を仮定しない。使われ方：零方向の合併の帰納。 -/
lemma subcomplex_sup_toPoint_localized_isIso {W : SSet.{u}} (A B : W.Subcomplex)
    (hA : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (A : SSet.{u}))))
    (hB : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (B : SSet.{u}))))
    (hI : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (A ⊓ B : W.Subcomplex).toSSet))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (A ⊔ B : W.Subcomplex).toSSet)) := by
  let i : (A ⊓ B : W.Subcomplex).toSSet ⟶ A := Subcomplex.homOfLE inf_le_left
  let j : (A ⊓ B : W.Subcomplex).toSSet ⟶ B := Subcomplex.homOfLE inf_le_right
  let a : (A : SSet.{u}) ⟶ (A ⊔ B : W.Subcomplex) := Subcomplex.homOfLE le_sup_left
  let b : (B : SSet.{u}) ⟶ (A ⊔ B : W.Subcomplex) := Subcomplex.homOfLE le_sup_right
  have hs : IsPushout i j a b :=
    (show Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from ⟨rfl, rfl⟩).isPushout
  have ht : IsPushout (𝟙 (𝟙_ SSet.{u})) (𝟙 _) (𝟙 _) (𝟙 _) :=
    IsPushout.of_vert_isIso ⟨by simp⟩
  exact KanPushoutCube.localized_isIso i j a b hs (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) ht
    (toUnit (A ⊓ B : W.Subcomplex).toSSet) (toUnit (A : SSet.{u})) (toUnit (B : SSet.{u}))
    (toUnit (A ⊔ B : W.Subcomplex).toSSet) (by simp) (by simp) (by simp) (by simp) hI hA hB

/-- 概要：追加で固定した零方向を持つ境界の有限合併。
方針：各選択方向を固定する像を格子の有限上限で合わせる。
規約：t は全ての部分に共通する零方向。使われ方：交差を含む帰納。 -/
def zeroDirectionsBoundary {r : ℕ} (s t : Finset (Fin r)) (X : StableModel.{u}) :
    (multiDiagonalCoreSConstruction r X).Subcomplex := s.sup (fun i => zeroDirectionsRange (insert i t) X)

/-- 概要：一方向を合併に加えると一つの像との上限になる。
方針：有限上限の挿入の式を使う。
規約：方向の重複は許す。使われ方：境界の有限帰納。 -/
lemma zeroDirectionsBoundary_insert {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsBoundary (insert i s) t X =
      zeroDirectionsRange (insert i t) X ⊔ zeroDirectionsBoundary s t X := by
  simp only [zeroDirectionsBoundary, Finset.sup_insert]

/-- 概要：一方向の像と境界の交差は、共通零方向にその方向を加えた境界。
方針：有限合併について帰納し、像の交差の計算と分配則を使う。
規約：部分複体の厳密な等号。使われ方：合併の弱可縮性。 -/
lemma zeroDirectionsBoundary_inf {r : ℕ} (i : Fin r) (s t : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsRange (insert i t) X ⊓ zeroDirectionsBoundary s t X =
      zeroDirectionsBoundary s (insert i t) X := by
  induction s using Finset.induction_on with
  | empty => simp [zeroDirectionsBoundary]
  | @insert j s hjs ih =>
    rw [zeroDirectionsBoundary_insert]
    have hd := subcomplex_inf_sup (zeroDirectionsRange (insert i t) X)
      (zeroDirectionsRange (insert j t) X) (zeroDirectionsBoundary s t X)
    rw [hd]
    rw [ih, zeroDirectionsBoundary_insert]
    congr 1
    rw [← zeroDirectionsRange_union]
    congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

/-- 概要：非空の零方向の境界の有限合併は弱可縮。
方針：全交差を同じ形の境界で表し、二つの部分と交差の pushout 比較で帰納する。
規約：共通の固定方向 t は空でもよい。使われ方：fat wedge 全体の collapse。 -/
lemma zeroDirectionsBoundary_toPoint_localized_isIso {r : ℕ} (s t : Finset (Fin r))
    (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (zeroDirectionsBoundary s t X : SSet.{u}))) := by
  induction s using Finset.induction_on generalizing t with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s his ih =>
    by_cases hse : s = ∅
    · subst s
      have he : zeroDirectionsBoundary (insert i ∅) t X = zeroDirectionsRange (insert i t) X := by
        unfold zeroDirectionsBoundary
        rw [Finset.insert_empty]
        exact Finset.sup_singleton
      rw [he]
      exact zeroDirectionsRange_toPoint_localized_isIso (insert i t) (Finset.insert_nonempty _ _) X
    · have hsn : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
      rw [zeroDirectionsBoundary_insert]
      apply subcomplex_sup_toPoint_localized_isIso
      · exact zeroDirectionsRange_toPoint_localized_isIso _ (Finset.insert_nonempty _ _) X
      · exact ih t hsn
      · rw [zeroDirectionsBoundary_inf]
        exact ih (insert i t) hsn

/-- 概要：全零方向の境界（fat wedge）。
方針：各単独零方向の像の有限合併を取る。
規約：反復数 r の内部で全方向を使う。使われ方：反復間の構造射の境界を潰す。 -/
def zeroDirectionsFatBoundary (r : ℕ) (X : StableModel.{u}) :
    (multiDiagonalCoreSConstruction r X).Subcomplex := zeroDirectionsBoundary Finset.univ ∅ X

/-- 概要：正の反復の全零方向の境界は弱可縮。
方針：全方向の有限集合が非空であることを使う。
規約：内部の交差の全次数を含む。使われ方：境界全体を潰す商の比較。 -/
lemma zeroDirectionsFatBoundary_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}))) :=
  zeroDirectionsBoundary_toPoint_localized_isIso Finset.univ ∅ ⟨0, Finset.mem_univ _⟩ X

end SerrePositivity.KST.SConstruction
