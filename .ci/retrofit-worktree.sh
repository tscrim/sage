#!/bin/sh
if [ $# != 2 ]; then
    echo >&2 "usage: $0 WORKTREE_NAME WORKTREE_DIRECTORY"
    echo >&2 "Ensures that the current working directory is a git repository,"
    echo >&2 "then makes WORKTREE_DIRECTORY a git worktree named WORKTREE_NAME."
fi
WORKTREE_NAME="$1"
WORKTREE_DIRECTORY="$2"

export GIT_AUTHOR_NAME="ci-sage workflow"
export GIT_AUTHOR_EMAIL="ci-sage@example.com"
export GIT_COMMITTER_NAME="$GIT_AUTHOR_NAME"
export GIT_COMMITTER_EMAIL="$GIT_AUTHOR_EMAIL"

# Set globally for other parts of the workflow
git config --global user.name "$GIT_AUTHOR_NAME"
git config --global user.email "$GIT_AUTHOR_EMAIL"

set -ex

# If actions/checkout downloaded our source tree using the GitHub REST API
# instead of with git (because do not have git installed in our image),
# we first make the source tree a repo.
if [ ! -d .git ]; then git init && git add -A && git commit --quiet -m "new"; fi

# Tag this state of the source tree "new". This is what we want to build and test.
git tag -f new

# Our container image contains a source tree in $WORKTREE_DIRECTORY with a full build of Sage.
# But $WORKTREE_DIRECTORY is not a git repository.
# We make $WORKTREE_DIRECTORY a worktree whose index is at tag "new".
# We then commit the current sources and set the tag "old". (This keeps all mtimes unchanged.)
# Then we update worktree and index with "git reset --hard new".
# (This keeps mtimes of unchanged files unchanged and mtimes of changed files newer than unchanged files.)
# Finally we reset the index to "old". (This keeps all mtimes unchanged.)
# The changed files now show up as uncommitted changes.
# The final "git add -N" makes sure that files that were added in "new" do not show
# as untracked files, which would be removed by "git clean -fx".
git worktree add --detach $WORKTREE_NAME
rm -rf $WORKTREE_DIRECTORY/.git && mv $WORKTREE_NAME/.git $WORKTREE_DIRECTORY/
rm -rf $WORKTREE_NAME && ln -s $WORKTREE_DIRECTORY $WORKTREE_NAME
if [ ! -f $WORKTREE_NAME/.gitignore ]; then cp .gitignore $WORKTREE_NAME/; fi
(cd $WORKTREE_NAME && git add -A && git commit --quiet --allow-empty -m "old" -a && git tag -f old && git reset --hard new && git reset --quiet old && git add -N . && git status)
