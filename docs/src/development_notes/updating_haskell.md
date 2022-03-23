
# Updating the Haskell library

The actual typechecker is written in Haskell and is available [here](https://github.com/DiffMu/DiffPrivacyInferenceHs).

That project is included in this one using `git subtree`. For future reference we describe how that is done.
We follow these [instructions](https://www.atlassian.com/git/tutorials/git-subtree).

## Adding the subtree
**NOTE** This only has to be done once; and has already been done. It is written here only for completeness.

Create new remote.
```
git remote add -f DiffPrivacyInferenceHs git@github.com:DiffMu/DiffPrivacyInferenceHs.git
```

Add the subtree.
```
git subtree add --prefix deps/DiffPrivacyInferenceHs DiffPrivacyInferenceHs main --squash
```




