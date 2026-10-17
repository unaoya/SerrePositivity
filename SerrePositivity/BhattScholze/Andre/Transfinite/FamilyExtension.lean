module

public import SerrePositivity.BhattScholze.Andre.Transfinite.FamilySaturation
public import SerrePositivity.BhattScholze.Andre.Transfinite.SingleRoot
@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    {σ : Type u} (f : σ → Polynomial R)
/-- ## 概要
固定基底 R の正次数モニック族の任意の一項は、任意の塔の代数からの拡大先で根を持つ。
BS Thm 7.14（著者版 p.61）の根添加の一段の存在。

## 方針
非零枝では元の多項式を係数射で移すと正次数モニックのままなので、一元根付き拡大を適用する。
初段の完全忠実平坦性は射の合成で保つ。零環枝では既に根がある。

## 規約
環と族の添字は Type u。入力は各多項式のモニック性と正次数のみ。
一段拡大 step 自体や、有限性・追加の平坦性・比較条件を仮定しない。

## 使われ方
指定された step と同じ型の証明を、Thm 7.14 の ω₁ 反復に入力する。
-/
theorem exists_familyRoot_successor (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree)
    (X : AndreTowerAlgebra R p) (s : σ) :
    ∃ (Y : AndreTowerAlgebra R p) (_ : X ⟶ Y), HasBasePolynomialRoot f Y s := by
  classical
  rcases subsingleton_or_nontrivial X with hz | hn
  · exact ⟨X, 𝟙 X, 0, hz.elim _ _⟩
  let := hn
  let P := (f s).map X.baseMap
  have hP : P.Monic := (hf s).map _
  have hPdeg : 0 < P.natDegree := by
    rw [(hf s).natDegree_map]
    exact hdeg s
  obtain ⟨T, hTinst, φ, ρ, hT, hφ, hroot⟩ :=
    exists_monicRootPerfectoidExtension X p X.perfectoid P hP hPdeg
  let := hTinst
  let β := φ.comp X.baseMap
  let Y : AndreTowerAlgebra R p :=
    ⟨T, β, hT, isCompletelyFaithfullyFlat_natCast_comp X.baseMap φ p X.flat hφ⟩
  refine ⟨Y, ⟨φ, rfl⟩, ρ, ?_⟩
  exact (Polynomial.eval₂_map _ _ _).symm.trans hroot

/-- ## 概要
perfectoid 環 R 上の任意の正次数モニック多項式族は、同じ p 完全忠実平坦な perfectoid 拡大内に根を持つ。
BS Thm 7.14（著者版 p.61）の根添加の一段の存在。

## 方針
各対象で一項の根を得る拡大を構成し、添字族より大きい後続基数による既証の飽和反復を使う。
終段の各根を選び、元の係数環射と perfectoid 性・完全忠実平坦性を取り出す。

## 規約
環と族の添字は Type u。入力は各多項式のモニック性と正次数のみ。
一段拡大 step 自体や、有限性・追加の平坦性・比較条件を仮定しない。

## 使われ方
指定された step と同じ型の証明を、Thm 7.14 の ω₁ 反復に入力する。
-/
theorem exists_monicFamilyRootedPerfectoidExtension (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) {σ : Type u} (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic ∧ 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  classical
  obtain ⟨X, hX⟩ := exists_allBasePolynomialRoots f
    (exists_familyRoot_successor f (fun s ↦ (hf s).1) (fun s ↦ (hf s).2)) hR
  change ∀ s, ∃ x : X, (f s).eval₂ X.baseMap x = 0 at hX
  choose ρ hρ using hX
  exact ⟨X, inferInstance, X.baseMap, ρ, X.perfectoid, X.flat, hρ⟩


end SerrePositivity.BhattScholze.Andre.Transfinite
