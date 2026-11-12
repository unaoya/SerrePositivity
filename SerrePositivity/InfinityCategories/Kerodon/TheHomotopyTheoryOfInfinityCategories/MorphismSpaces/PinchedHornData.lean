module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearPullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFaces
public import Mathlib.Data.Finset.Sort

/-! # 右 pinched ホーンの線形成分の回収

概要：ホーンの利用可能な面から線形成分を回収し、面の選択によらないことを示す。
方針：共通の部分集合への制限をホーン写像の自然性で比較する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：直接の線形ホーン充填の既知成分。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：利用可能なホーン面の線形成分族。
方針：実際の右 pinched 単体から既存の線形表示で成分を回収する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：ホーンの既知の線形データ。 -/
def faceData {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (j : Fin (n + 2)) (hji : j ≠ i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (σ.app _ (SSet.horn.face i j hji))

/-- 概要：二面の同じ大域部分集合に対応する線形成分は一致する。
方針：一方の集合を順序付きで列挙し、共通のホーン単体への二つの制限を比較する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：既知成分の面の選択独立性。 -/
lemma face_component_eq {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (j l : Fin (n + 2)) (hji : j ≠ i) (hli : l ≠ i)
    (J L : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hL : L.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (hk' : k = 1 - (L.card : ℤ))
    (hImage : J.image j.succAbove = L.image l.succAbove) :
    (faceData σ j hji).component J k hJ hk = (faceData σ l hli).component L k hL hk' := by
  let r := J.card - 1
  have hcard : J.card = r + 1 := by have := hJ.card_pos; omega
  let e := J.orderEmbOfFin hcard
  let φ : ⦋r⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom e.toOrderHom
  let θ : ⦋r⦌ ⟶ ⦋n + 1⦌ := φ ≫ SimplexCategory.δ j
  have hθj : ∀ a, θ.toOrderHom a ≠ j := fun a => Fin.succAbove_ne j (e a)
  have hθl : ∀ a, θ.toOrderHom a ≠ l := by
    intro a ha
    have hm : θ.toOrderHom a ∈ J.image j.succAbove :=
      Finset.mem_image.mpr ⟨e a, J.orderEmbOfFin_mem hcard a, rfl⟩
    rw [hImage, ha] at hm
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hm
    exact Fin.succAbove_ne l b hb
  let β := SimplexCategory.factor_δ θ l
  have hβδ := SimplexCategory.factor_δ_spec θ l hθl
  have hβ : ∀ a, l.succAbove (β.toOrderHom a) = j.succAbove (φ.toOrderHom a) := by
    intro a
    exact congrArg (fun f => f.toOrderHom a) hβδ
  have hβinj : Function.Injective β.toOrderHom := by
    intro a b hab
    apply e.injective
    apply j.succAboveOrderEmb.injective
    exact (hβ a).symm.trans ((congrArg l.succAbove hab).trans (hβ b))
  have hφ : SimplexCategory.factor_δ θ j = φ := by
    ext a : 3
    apply j.succAboveOrderEmb.injective
    exact congrArg (fun f => f.toOrderHom a) (SimplexCategory.factor_δ_spec θ j hθj)
  have hres : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback φ.toOrderHom (faceData σ j hji) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β.toOrderHom (faceData σ l hli) := by
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFaces.restriction_independent i σ θ j l hji hli hθj hθl
    rw [hφ] at hh
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData hh
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((σ.app _ (SSet.horn.face i j hji)).pullback φ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((σ.app _ (SSet.horn.face i l hli)).pullback β) at he
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_pullback, faceData] using he
  let E : Finset (Fin (r + 1)) := Finset.univ
  have hE : E.Nonempty := ⟨0, Finset.mem_univ _⟩
  have hkE : k = 1 - (E.card : ℤ) := by
    simpa only [E, Finset.card_univ, Fintype.card_fin, ← hcard] using hk
  have hαI : E.image φ.toOrderHom = J := J.image_orderEmbOfFin_univ hcard
  have hβI : E.image β.toOrderHom = L := by
    apply Finset.image_injective l.succAboveOrderEmb.injective
    calc
      (E.image β.toOrderHom).image l.succAbove =
          E.image (fun a => l.succAbove (β.toOrderHom a)) := Finset.image_image
      _ = E.image (fun a => j.succAbove (φ.toOrderHom a)) :=
        congrArg (fun f => E.image f) (funext hβ)
      _ = (E.image φ.toOrderHom).image j.succAbove := by rw [Finset.image_image]; rfl
      _ = J.image j.succAbove := by rw [hαI]
      _ = L.image l.succAbove := hImage
  have he := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y r => f.component E k hE hkE) hres
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ e.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hβinj.injOn] at he
  simpa only [hαI, hβI] using he

/-- 概要：全体集合と欠けた面以外の非空部分集合の成分を回収する。
方針：集合を含む利用可能な面を選び、その面の順序埋め込みの逆像で読む。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：直接の線形充填で保持する既知成分。 -/
def recoverComponent {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) : GradedHom A x y k := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace I i hfull hmissing
  have hji : j ≠ i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_ne I i hfull hmissing
  have hj : j ∉ I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hfull hmissing
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  exact (faceData σ j hji).component J k
    (Finset.card_pos.mp (by rw [hcard]; exact hI.card_pos)) (by rw [hcard]; exact hk)

/-- 概要：回収した成分は、その集合を含む任意の利用可能な面の成分と一致する。
方針：回収に選んだ面と指定した面の大域像を比較し、面の選択独立性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：回収族の各面への制限の検証。 -/
lemma recoverComponent_eq_face {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i)
    (j : Fin (n + 2)) (hji : j ≠ i) (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) (hk' : k = 1 - (J.card : ℤ)) (hImage : J.image j.succAbove = I) :
    recoverComponent σ I k hI hk hfull hmissing = (faceData σ j hji).component J k hJ hk' := by
  unfold recoverComponent
  apply face_component_eq σ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hfull hmissing)).trans
    hImage.symm

/-- 概要：利用可能な面の像は二つの未知集合のいずれでもない。
方針：飛ばした頂点が像に入らないことを用いる。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：面上の回収の条件分岐を確定する。 -/
lemma image_known {n : ℕ} {i : Fin (n + 2)} (j : Fin (n + 2)) (hji : j ≠ i)
    (J : Finset (Fin (n + 1))) :
    J.image j.succAbove ≠ Finset.univ ∧ J.image j.succAbove ≠ Finset.univ.erase i := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face _ i).mp
  refine ⟨j, hji, ?_⟩
  rintro hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
  exact Fin.succAbove_ne j a ha

/-- 概要：既知成分を回収し、全体集合と欠けた面の二成分を零とした線形族。
方針：未知の二集合だけを除き、それ以外は利用可能な面から評価する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：欠けた面を明示解に置き換える前の族。 -/
def knownData {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1) := fun t =>
  if hf : t.val.1 ≠ Finset.univ then
    if hm : t.val.1 ≠ Finset.univ.erase i then
      recoverComponent σ t.val.1 t.val.2 t.property.1 t.property.2 hf hm
    else 0
  else 0

/-- 概要：既知族を利用可能な面へ引き戻すと元のホーン面の線形成分族に戻る。
方針：各部分集合の像が既知であることと回収の面との一致を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：既知の方程式とホーンとの面の一致の回収。 -/
lemma knownData_pullback_face {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (knownData σ) = faceData σ j hji := by
  funext t
  rcases t with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (knownData σ)).component J k hJ hk =
    (faceData σ j hji).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  have hf : J.image j.succAboveOrderEmb.toOrderHom ≠ Finset.univ := (image_known j hji J).1
  have hm : J.image j.succAboveOrderEmb.toOrderHom ≠ Finset.univ.erase i := (image_known j hji J).2
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, knownData, dite_eq_left hf, dite_eq_left hm]
  exact recoverComponent_eq_face σ _ _ _ _ hf hm j hji J hJ hk rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
