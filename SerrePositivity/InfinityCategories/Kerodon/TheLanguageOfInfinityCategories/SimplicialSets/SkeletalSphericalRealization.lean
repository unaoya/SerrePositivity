module


public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalCochainExtension

/-!
概要：非退化単体ごとの球面的代表を実際の骨格上の射として実現する。
方針：各セルで指定した代表を低い骨格の定数射へ付着 pushout で貼る。
規約：低い骨格上では厳密に定数である。
使われ方：Goerss–Jardine I §7、VIII §1。係数 cochain から幾何への構成。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section

universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalSphericalRealization
end SerrePositivity.KST.Spectra.SkeletalSphericalRealization
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletalSphericalRealization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セルの骨格内の特徴射は、その単体の持ち上げの Yoneda 射。
方針：全体への単射を後合成して標準の特徴射の計算を使う。
規約：セルの次元 d は任意。
使われ方：Goerss–Jardine VIII §1。実現した射のセルでの値の検査。 -/
theorem characteristic_eq_yoneda (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    c.ιSigmaStdSimplex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristicMap K d =
      SSet.yonedaEquiv.symm
        (⟨c.simplex, K.mem_skeleton _⟩ : (K.skeleton (d + 1) : SSet.{u}) _⦋d⦌) := by
  apply (cancel_mono (K.skeleton (d + 1)).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_characteristicMap_ι, yonedaEquiv_symm_comp]
  rfl

/-- 概要：任意のセルごとの境界定数単体の族は骨格上の射として実現できる。
方針：指定した単体をセルの余積へ束ね、低い骨格の定数射へ pushout で貼る。
規約：単体の代表を厳密に実現し、低い骨格上も厳密に定数。
使われ方：Goerss–Jardine I §7、VIII §1。cochain の代表を実際の射へ変換する。 -/
theorem exists_map {K X : SSet.{u}} {d : ℕ} {x : X _⦋0⦌}
    (a : K.nonDegenerate d → X.PtSimplex d x) :
    ∃ f : (K.skeleton (d + 1) : SSet.{u}) ⟶ X,
      Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ d)) ≫ f = SSet.const x ∧
      ∀ s : K.nonDegenerate d,
        SSet.yonedaEquiv.symm
          (⟨s.val, K.mem_skeleton _⟩ : (K.skeleton (d + 1) : SSet.{u}) _⦋d⦌) ≫ f =
            (a s).map := by
  let φ := fun c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d ↦
    (a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K d c)).map
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.attachingMap K d ≫ SSet.const x =
      relativeCellComplexOfMono.l (K.skeleton d).ι d ≫ Sigma.desc φ := by
    ext c : 1
    simp only [relativeCellComplexOfMono.l, Sigma.ι_map_assoc, Sigma.ι_comp_desc, comp_const]
    change SSet.const x = (boundary d).ι ≫ (a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K d c)).map
    rw [(a _).comm, Subcomplex.ofSimplex_ι, comp_const]
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K d).desc (SSet.const x) (Sigma.desc φ) hw
  refine ⟨f, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K d).inl_desc _ _ _, ?_⟩
  intro s
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K d).symm s
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K d c = s :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K d).apply_symm_apply s
  have hs : c.simplex = s.val := congrArg Subtype.val hc
  have hv := congrArg (fun k ↦ c.ιSigmaStdSimplex ≫ k)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.isPushout K d).inr_desc (SSet.const x) (Sigma.desc φ) hw)
  simp only [Sigma.ι_comp_desc] at hv
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.characteristic_eq_yoneda] at hv
  simpa only [φ, hc, hs] using hv

/-- 概要：低い骨格で定数の射はその骨格に含まれる低次元単体で定数。
方針：低次元単体を低い骨格へ持ち上げ、制限の等式を後合成する。
規約：低次元の実際の次数は n + 1。
使われ方：Goerss–Jardine VIII §1。実現した射の係数を定義する条件。 -/
theorem lower_constant {K X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ X)
    (hf : Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 2))) ≫ f = SSet.const x)
    (s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌) :
    SSet.yonedaEquiv.symm s ≫ f = SSet.const x := by
  let t : (K.skeleton (n + 2) : SSet.{u}) _⦋n + 1⦌ := ⟨s.val, K.mem_skeleton _⟩
  have he : SSet.yonedaEquiv.symm t ≫
      Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 2))) =
        SSet.yonedaEquiv.symm s := by rw [yonedaEquiv_symm_comp]; rfl
  rw [← he, Category.assoc, hf, comp_const]

/-- 概要：任意の高次ホモトピー群係数の cochain を実際の骨格上の射で実現できる。
方針：商の各類の代表を選び、そのセルの代表を貼り合わせる。
規約：実際の次数は n + 2。定数条件の証明も一緒に構成する。
使われ方：Goerss–Jardine I §7、VIII §1。係数から幾何への写像の存在。 -/
theorem exists_realization {K X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}
    (a : K.nonDegenerate (n + 2) → Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x)) :
    ∃ (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ X)
      (h : ∀ s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
        SSet.yonedaEquiv.symm s ≫ f = SSet.const x),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h = a := by
  choose r hr using fun s ↦ Quotient.exists_rep (Additive.toMul (a s))
  obtain ⟨f, hf, hfr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.exists_map r
  refine ⟨f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf, ?_⟩
  funext s
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s.val = r s := by
    apply RelativeMorphism.ext
    exact hfr s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s.val) = a s
  rw [hs]
  exact congrArg Additive.ofMul (hr s)

/-- 概要：任意の高次群係数の cocycle を一つ高い骨格まで定義された射で実現できる。
方針：セルごとの代表で cochain を実現し、交代微分の零性から一段延長する。
規約：最初の骨格の係数が指定した a と厳密に一致する。
使われ方：Goerss–Jardine I §7、VIII §1。cocycle の幾何的な実現。 -/
theorem exists_extended_realization {K X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}
    (a : K.nonDegenerate (n + 2) → Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2) a = 0) :
    ∃ (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ X)
      (h : ∀ s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
        SSet.yonedaEquiv.symm s ≫ f = SSet.const x)
      (g : (K.skeleton (n + 4) : SSet.{u}) ⟶ X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h = a ∧
        Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 3))) ≫ g = f := by
  obtain ⟨f, h, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.exists_realization a
  have hz : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) = 0 := by rw [hf]; exact ha
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.exists_extension_of_differential_eq_zero f h hz
  exact ⟨f, h, g, hf, hg⟩

end

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
