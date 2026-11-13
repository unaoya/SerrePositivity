from pathlib import Path

base=Path('/tmp/BSW13AlmostTensor.lean')
s=base.read_text().rstrip()
probe=Path('/tmp/bsw13-connectivity-lemmas.lean').read_text()
addition=probe[probe.index('namespace SerrePositivity.InfinityCategories.Derived'):]
i=addition.index('private theorem complexSemifree_kFlat')
j=addition.index('abbrev quotientTensor',i)
addition=addition[:i]+addition[j:]
addition=addition.replace('def IsConnectiveAt', '''/-- BS 著者版 Lemma 10.5 の連結性を、コホモロジー次数の上界で表す。 -/
def IsConnectiveAt''')
docs={
  'abbrev quotientTensor':'完備導来テンソルの左入力に古典的な perfectoid 商を置く。',
  'theorem isConnectiveAt_iff_isLE':'頂点の連結性は通常の導来圏の t 構造で判定できる。',
  'theorem isLE_moduleHeartVertex':'離散加群の頂点は零次より上のコホモロジーを持たない。',
  'theorem quotientTensor_isAlmostZero':'商との完備テンソルの各コホモロジーは商環上の加群になる。',
  'theorem almostConnective_of_kernelTensor_connective':'核との完備テンソルが連結なら、元の複体は almost 連結になる。',
  'theorem connective_of_kernelTensor_and_quotientTensor':'核と商で得る二つの完備テンソルから元の複体の連結性を復元する。',
}
for name, doc in docs.items():
    addition=addition.replace(name, f'/-- {doc} -/\n'+name)
addition=addition.replace('  -- This preliminary version uses the one-sided computation of the tensor.\n','')
addition=addition.replace('  let K := perfectoidKernel p R hR J\n  let B := QuotientPerfectoidization R J p hR\n  let q :=','  let B := QuotientPerfectoidization R J p hR\n  let q :=',1)
s=s+'\n\n'+addition
base.write_text(s)

s=Path('/tmp/bsw13-truncation-probe.lean').read_text()
s='module\n\n'+s.replace('import ', 'public import ')
s='\n'.join(line for line in s.splitlines() if not line.startswith('#print axioms'))+'\n'
s=s.replace('noncomputable section','''/-! # 非有界複体の almost 零性と連結性

## 概要
BS 著者版 Proposition 10.4 の複体の同値と Lemma 10.5 の連結性の判定。

## 方針
上への切り捨ての差を一つのコホモロジー加群として扱い、固定した核の射影分解を
テンソルする。非有界の複体へは、各冪の Koszul 簡約で逐次余極限を取って移す。

## 規約
完備テンソルには元の半自由代表を使う。コホモロジー次数の零以下を連結とする。

## 使われ方
BS 著者版 Theorem 10.9 と Theorem 10.11 の almost 連結性の議論。
-/

@[expose] public noncomputable section''')
s=s.replace('theorem isAlmostZero_iff_completedTensor_isZero\n    (_hJ',
'''/-- BS 著者版 Proposition 10.4 の完備複体の almost 零性を、核とのテンソルで判定する。 -/
set_option linter.unusedVariables false in
theorem isAlmostZero_iff_completedTensor_isZero
    (hJ''')
s=s.replace('theorem kernelTensor_isLE_of_almostConnective',
'''/-- almost 連結性から、核との完備テンソルの連結性を得る。 -/
theorem kernelTensor_isLE_of_almostConnective''')
s=s.replace('end SerrePositivity.BhattScholze.Almost','''/--
BS 著者版 Lemma 10.5 の比較に使う。almost 連結性を核との完備テンソルで判定する。
-/
set_option linter.unusedVariables false in
theorem isAlmostConnective_iff_completedTensor_connective
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsAlmostConnective p R hR J M ↔ Derived.IsConnectiveAt R 0 (kernelTensor p R hR J M) :=
  ⟨fun h ↦ (isConnectiveAt_iff_isLE 0 _).mpr
    (kernelTensor_isLE_of_almostConnective p hR J M h),
    almostConnective_of_kernelTensor_connective p hR J M hM⟩

/-- BS 著者版 Lemma 10.5。連結性を商との完備テンソルと almost 連結性で判定する。 -/
theorem connective_iff_almost
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    Derived.IsConnectiveAt R 0 M ↔ Derived.IsConnectiveAt R 0 (quotientTensor p hR J M) ∧
      IsAlmostConnective p R hR J M := by
  constructor
  · intro h
    refine ⟨(isConnectiveAt_iff_isLE 0 _).mpr ?_, ?_⟩
    · have hB := isLE_moduleHeartVertex (ModuleCat.of R (QuotientPerfectoidization R J p hR))
      have hM' := (isConnectiveAt_iff_isLE 0 M).mp h
      simpa only [add_zero] using completedModuleTensor_isLE p _ M 0 0 hB hM'
    · intro i hi
      exact SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
        (fun _ _ _ ↦ (h i hi).elim _ _)
  · rintro ⟨hB, hK⟩
    exact connective_of_kernelTensor_and_quotientTensor p hR J M hM
      ((isAlmostConnective_iff_completedTensor_connective p hR J hJ M hM).mp hK) hB

end SerrePositivity.BhattScholze.Almost''')
s=s.replace('\n\n\n','\n\n')
for name, desc in {
    'private def goodTruncationMap':'上への切り捨ての包含を、元の複体への写像の自然性から作る。',
    'private def goodTruncationIsColimit':'各次数で包含がやがて同型になるので、元の複体が余極限となる。',
    'private def goodTruncationLayerIso':'隣接する二つの切り捨ての差は、追加した次数のコホモロジー加群。',
    'private theorem completedTensorRight_truncations_are_zero':'各次数で、十分低い上界から有限回だけ切り捨ての上界を上げる。',
    'private theorem completedTensorRight_isZero_of_homology':'完備化の前に Koszul 簡約を取り、完全な逐次余極限で消滅を移す。',
}.items():
    s=s.replace(name, f'/-- {desc} -/\n'+name)
s=s.replace('  exact (F.map_isZero (DerivedCategory.Q.map_isZero (isZero_zero _))).of_iso (asIso (F.map (DerivedCategory.Q.map f)))',
    '  exact (F.map_isZero (DerivedCategory.Q.map_isZero (isZero_zero _))).of_iso\n    (asIso (F.map (DerivedCategory.Q.map f)))')
s=s.replace('    (derivedInfinityHomotopyEquivalence R).counitIso.app', '    (derivedInfinityHomotopyEquivalence R).counitIso.app')
Path('/tmp/BSW13AlmostTensorForward.lean').write_text(s)
for p in [base, Path('/tmp/BSW13AlmostTensorForward.lean')]:
    for i,l in enumerate(p.read_text().splitlines(),1):
        if len(l)>100: print(p.name,i,len(l),l)
